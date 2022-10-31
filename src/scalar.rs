// Limbs of the secp256k1 order.
pub const N_0_32: u32 = 0xD0364141;
pub const N_1_32: u32 = 0xBFD25E8C;
pub const N_2_32: u32 = 0xAF48A03B;
pub const N_3_32: u32 = 0xBAAEDCE6;
pub const N_4_32: u32 = 0xFFFFFFFE;
pub const N_5_32: u32 = 0xFFFFFFFF;
pub const N_6_32: u32 = 0xFFFFFFFF;
pub const N_7_32: u32 = 0xFFFFFFFF;

// Limbs of 2^256 minus the secp256k1 order.
pub const N_C_0_32: u32 = !N_0_32 + 1;
pub const N_C_1_32: u32 = !N_1_32;
pub const N_C_2_32: u32 = !N_2_32;
pub const N_C_3_32: u32 = !N_3_32;
pub const N_C_4_32: u32 = 1;

// Limbs of half the secp256k1 order.
pub const N_H_0_32: u32 = 0x681B20A0;
pub const N_H_1_32: u32 = 0xDFE92F46;
pub const N_H_2_32: u32 = 0x57A4501D;
pub const N_H_3_32: u32 = 0x5D576E73;
pub const N_H_4_32: u32 = 0xFFFFFFFF;
pub const N_H_5_32: u32 = 0xFFFFFFFF;
pub const N_H_6_32: u32 = 0xFFFFFFFF;
pub const N_H_7_32: u32 = 0x7FFFFFFF;

/// A scalar modulo the group order of the secp256k1 curve.
///
/// The scalar is made of 8 digits (32bits integers).
#[derive(Copy)]
pub struct Scalar32 {
    pub d: [u32; 8],
}

impl Scalar32 {
    /// Returns a Scalar32.
    ///
    /// # Arguments
    ///
    /// * `digits` - Array of 8 32bits integers.
    pub fn new(digits: [u32; 8]) -> Scalar32 {
        Scalar32 { d: digits }
    }
}

impl Clone for Scalar32 {
    /// Returns a clone of the Scalar32 instance.
    fn clone(&self) -> Scalar32 {
        Scalar32 { d: self.d }
    }
}

impl Scalar32 {
    /// Sets the scalar to 0.
    pub fn clear(&mut self) {
        self.d[0] = 0;
        self.d[1] = 0;
        self.d[2] = 0;
        self.d[3] = 0;
        self.d[4] = 0;
        self.d[5] = 0;
        self.d[6] = 0;
        self.d[7] = 0;
    }

    /// Sets the scalar to a 32bits integer.
    ///
    /// # Arguments
    ///
    /// * `integer` - 32bits integer to set the Scalar32 to.
    pub fn set_int(&mut self, integer: u32) {
        self.d[0] = integer;
        self.d[1] = 0;
        self.d[2] = 0;
        self.d[3] = 0;
        self.d[4] = 0;
        self.d[5] = 0;
        self.d[6] = 0;
        self.d[7] = 0;
    }

    /// Returns a sequence of bits from the Scalar32.
    ///
    /// The length of this sequence must be able to fill
    /// an unsigned 32bits integer.
    ///
    /// # Arguments
    ///
    /// * `offset` - Offset of the sequence first bit.
    /// * `count` - Number of bits to return.
    ///
    /// # Errors
    ///
    /// Returns a String error if :
    /// - count is 0 : nonsense to get 0 bits.
    /// - count is > 32 : the sequence must fit a 32bits integer.
    /// - offset + count > 256 : overflow.
    pub fn get_bits(&self, offset: u32, count: u32) -> Result<u32, String> {
        if count == 0 || count > 32 {
            return Err(format!("count must be in ]0, 32], got {}", count));
        }
        if offset + count > 256 {
            return Err(format!(
                "offset + count must be in [1, 256], got {}",
                offset + count
            ));
        }
        if (offset + count - 1) >> 5 == offset >> 5 {
            Ok((self.d[(offset >> 5) as usize] >> (offset & 0x1F)) & ((1 << count) - 1))
        } else {
            Ok(((self.d[(offset >> 5) as usize] >> (offset & 0x1F))
                | (self.d[((offset >> 5) + 1) as usize] << (32 - (offset & 0x1F))))
                & ((1 << count) - 1))
        }
    }

    /// Checks if the Scalar32 overflows.
    ///
    /// In our context, a scalar overflows if it exceeds or
    /// is equal to the limbs of the secp256k1 order.
    ///
    /// Returns 1 if the scalar is >= N, else returns 0.
    pub fn check_overflow(&self) -> bool {
        let mut yes: bool = false;
        let mut no: bool = false;
        no |= self.d[7] < N_7_32;
        no |= self.d[6] < N_6_32;
        no |= self.d[5] < N_5_32;
        no |= self.d[4] < N_4_32;
        yes |= (self.d[4] > N_4_32) & !no;
        no |= (self.d[3] < N_3_32) & !yes;
        yes |= (self.d[3] > N_3_32) & !no;
        no |= (self.d[2] < N_2_32) & !yes;
        yes |= (self.d[2] > N_2_32) & !no;
        no |= (self.d[1] < N_1_32) & !yes;
        yes |= (self.d[1] > N_1_32) & !no;
        yes |= (self.d[0] >= N_0_32) & !no;
        yes
    }

    /// Reduces the Scalar32 modulo the group order of the secp256k1 curve.
    ///
    /// Will not perform reduction if the the scalar does not overflow.
    pub fn reduce(&mut self) {
        if self.check_overflow() {
            let mut tmp: u64;
            tmp = self.d[0] as u64 + N_C_0_32 as u64;
            self.d[0] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += self.d[1] as u64 + N_C_1_32 as u64;
            self.d[1] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += self.d[2] as u64 + N_C_2_32 as u64;
            self.d[2] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += self.d[3] as u64 + N_C_3_32 as u64;
            self.d[3] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += self.d[4] as u64 + N_C_4_32 as u64;
            self.d[4] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += self.d[5] as u64;
            self.d[5] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += self.d[6] as u64;
            self.d[6] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += self.d[7] as u64;
            self.d[7] = (tmp & 0xFFFFFFFF) as u32;
        }
    }

    /// Adds two Scalar32 together.
    ///
    /// If the result overflows, if will be reduced modulo
    /// the group order of the secp256k1 curve.
    ///
    /// # Arguments
    ///
    /// * `a` - Reference to the first Scalar32 member.
    /// * `b` - Reference to the second Scalar32 member.
    pub fn add(a: &Scalar32, b: &Scalar32) -> Scalar32 {
        let mut result: Scalar32 = Scalar32::new([0, 0, 0, 0, 0, 0, 0, 0]);
        let mut tmp: u64 = (a.d[0] + b.d[0]) as u64;
        result.d[0] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += (a.d[1] + b.d[1]) as u64;
        result.d[1] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += (a.d[2] + b.d[2]) as u64;
        result.d[2] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += (a.d[3] + b.d[3]) as u64;
        result.d[3] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += (a.d[4] + b.d[4]) as u64;
        result.d[4] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += (a.d[5] + b.d[5]) as u64;
        result.d[5] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += (a.d[6] + b.d[6]) as u64;
        result.d[6] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += (a.d[7] + b.d[7]) as u64;
        result.d[7] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        result.reduce();
        result
    }

    /// Conditionally adds a power of two to a scalar.
    ///
    /// The result is not allowed to overflow.
    ///
    /// # Arguments
    ///
    /// * `bit` - TODO: Explain.
    /// * `flag` - TODO: Explain.
    ///
    /// # Errors
    ///
    /// Returns a String error if :
    /// - bit is not in [0, 255].
    /// - result exceeds 256bits.
    /// - result overflows.
    pub fn cond_add_bit(&mut self, mut bit: u32, flag: i32) -> Result<(), String> {
        if bit > 255 {
            return Err(format!("expected bit in [0, 255], got {}", bit));
        }
        let mut tmp: u64;
        let mut result: Scalar32 = self.clone();
        bit += (flag as u32 - 1) & 0x100;
        tmp = result.d[0] as u64 + ((((bit >> 5) == 0) as u32) << (bit & 0x1F)) as u64;
        result.d[0] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += result.d[1] as u64 + ((((bit >> 5) == 1) as u32) << (bit & 0x1F)) as u64;
        result.d[1] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += result.d[2] as u64 + ((((bit >> 5) == 2) as u32) << (bit & 0x1F)) as u64;
        result.d[2] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += result.d[3] as u64 + ((((bit >> 5) == 3) as u32) << (bit & 0x1F)) as u64;
        result.d[3] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += result.d[4] as u64 + ((((bit >> 5) == 4) as u32) << (bit & 0x1F)) as u64;
        result.d[4] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += result.d[5] as u64 + ((((bit >> 5) == 5) as u32) << (bit & 0x1F)) as u64;
        result.d[5] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += result.d[6] as u64 + ((((bit >> 5) == 6) as u32) << (bit & 0x1F)) as u64;
        result.d[6] = (tmp & 0xFFFFFFFF) as u32;
        tmp >>= 32;
        tmp += result.d[7] as u64 + ((((bit >> 5) == 7) as u32) << (bit & 0x1F)) as u64;
        result.d[7] = (tmp & 0xFFFFFFFF) as u32;
        if (tmp >> 32) != 0 {
            return Err(format!("result exceeds the size of a 256bits integer"));
        }
        if result.check_overflow() {
            return Err(format!("result overflows"));
        }
        *self = result;
        Ok(())
    }

    /// Sets a scalar from a big endian byte array.
    ///
    /// The scalar will be reduced modulo group order n.
    ///
    /// # Arguments
    ///
    /// * `byte_array` - 32 bytes array.
    pub fn set_byte_array(&mut self, byte_array: [u8; 32]) {
        self.d[0] = byte_array[31] as u32
            | (byte_array[30] as u32) << 8
            | (byte_array[29] as u32) << 16
            | (byte_array[28] as u32) << 24;
        self.d[1] = byte_array[27] as u32
            | (byte_array[26] as u32) << 8
            | (byte_array[25] as u32) << 16
            | (byte_array[24] as u32) << 24;
        self.d[2] = byte_array[23] as u32
            | (byte_array[22] as u32) << 8
            | (byte_array[21] as u32) << 16
            | (byte_array[20] as u32) << 24;
        self.d[3] = byte_array[19] as u32
            | (byte_array[18] as u32) << 8
            | (byte_array[17] as u32) << 16
            | (byte_array[16] as u32) << 24;
        self.d[4] = byte_array[15] as u32
            | (byte_array[14] as u32) << 8
            | (byte_array[13] as u32) << 16
            | (byte_array[12] as u32) << 24;
        self.d[5] = byte_array[11] as u32
            | (byte_array[10] as u32) << 8
            | (byte_array[9] as u32) << 16
            | (byte_array[8] as u32) << 24;
        self.d[6] = byte_array[7] as u32
            | (byte_array[6] as u32) << 8
            | (byte_array[5] as u32) << 16
            | (byte_array[4] as u32) << 24;
        self.d[7] = byte_array[3] as u32
            | (byte_array[2] as u32) << 8
            | (byte_array[1] as u32) << 16
            | (byte_array[0] as u32) << 24;
        self.reduce();
    }

    /// Returns the scalar in a big endian byte array format.
    pub fn get_byte_array(&self) -> [u8; 32] {
        let mut byte_array: [u8; 32] = [0; 32];
        byte_array[0] = (self.d[7] >> 24) as u8;
        byte_array[1] = (self.d[7] >> 16) as u8;
        byte_array[2] = (self.d[7] >> 8) as u8;
        byte_array[3] = self.d[7] as u8;
        byte_array[4] = (self.d[6] >> 24) as u8;
        byte_array[5] = (self.d[6] >> 16) as u8;
        byte_array[6] = (self.d[6] >> 8) as u8;
        byte_array[7] = self.d[6] as u8;
        byte_array[8] = (self.d[5] >> 24) as u8;
        byte_array[9] = (self.d[5] >> 16) as u8;
        byte_array[10] = (self.d[5] >> 8) as u8;
        byte_array[11] = self.d[5] as u8;
        byte_array[12] = (self.d[4] >> 24) as u8;
        byte_array[13] = (self.d[4] >> 16) as u8;
        byte_array[14] = (self.d[4] >> 8) as u8;
        byte_array[15] = self.d[4] as u8;
        byte_array[16] = (self.d[3] >> 24) as u8;
        byte_array[17] = (self.d[3] >> 16) as u8;
        byte_array[18] = (self.d[3] >> 8) as u8;
        byte_array[19] = self.d[3] as u8;
        byte_array[20] = (self.d[2] >> 24) as u8;
        byte_array[21] = (self.d[2] >> 16) as u8;
        byte_array[22] = (self.d[2] >> 8) as u8;
        byte_array[23] = self.d[2] as u8;
        byte_array[24] = (self.d[1] >> 24) as u8;
        byte_array[25] = (self.d[1] >> 16) as u8;
        byte_array[26] = (self.d[1] >> 8) as u8;
        byte_array[27] = self.d[1] as u8;
        byte_array[28] = (self.d[0] >> 24) as u8;
        byte_array[29] = (self.d[0] >> 16) as u8;
        byte_array[30] = (self.d[0] >> 8) as u8;
        byte_array[31] = self.d[0] as u8;
        byte_array
    }

    /// Checks if the Scalar32 is zero.
    ///
    /// Returns true if it is, false otherwise.
    pub fn is_zero(&self) -> bool {
        if (self.d[0]
            | self.d[1]
            | self.d[2]
            | self.d[3]
            | self.d[4]
            | self.d[5]
            | self.d[6]
            | self.d[7])
            == 0
        {
            true
        } else {
            false
        }
    }

    /// Checks if the Scalar32 is one.
    ///
    /// Returns true if it is, false otherwise.
    pub fn is_one(&self) -> bool {
        if ((self.d[0] ^ 1)
            | self.d[1]
            | self.d[2]
            | self.d[3]
            | self.d[4]
            | self.d[5]
            | self.d[6]
            | self.d[7])
            == 0
        {
            true
        } else {
            false
        }
    }

    /// Negates the Scalar32.
    ///
    /// The scalar in replaced by its complement modulo the group order.
    pub fn negate(&mut self) {
        if !self.is_zero() {
            let mut tmp: u64 = !self.d[0] as u64 + N_0_32 as u64 + 1;
            self.d[0] = tmp as u32;
            tmp >>= 32;
            tmp += !self.d[1] as u64 + N_1_32 as u64;
            self.d[1] = tmp as u32;
            tmp >>= 32;
            tmp += !self.d[2] as u64 + N_2_32 as u64;
            self.d[2] = tmp as u32;
            tmp >>= 32;
            tmp += !self.d[3] as u64 + N_3_32 as u64;
            self.d[3] = tmp as u32;
            tmp >>= 32;
            tmp += !self.d[4] as u64 + N_4_32 as u64;
            self.d[4] = tmp as u32;
            tmp >>= 32;
            tmp += !self.d[5] as u64 + N_5_32 as u64;
            self.d[5] = tmp as u32;
            tmp >>= 32;
            tmp += !self.d[6] as u64 + N_6_32 as u64;
            self.d[6] = tmp as u32;
            tmp >>= 32;
            tmp += !self.d[7] as u64 + N_7_32 as u64;
            self.d[7] = tmp as u32;
        }
    }

    /// Checks whether a scalar is higher than the group order divided by 2.
    ///
    /// Returns true if it is, false otherwise.
    pub fn is_high(&self) -> bool {
        let mut yes: bool = false;
        let mut no: bool = false;
        no |= self.d[7] < N_H_7_32;
        yes |= (self.d[7] > N_H_7_32) & !no;
        no |= (self.d[6] < N_H_6_32) & !yes;
        no |= (self.d[5] < N_H_5_32) & !yes;
        no |= (self.d[4] < N_H_4_32) & !yes;
        no |= (self.d[3] < N_H_3_32) & !yes;
        yes |= (self.d[3] > N_H_3_32) & !no;
        no |= (self.d[2] < N_H_2_32) & !yes;
        yes |= (self.d[2] > N_H_2_32) & !no;
        no |= (self.d[1] < N_H_1_32) & !yes;
        yes |= (self.d[1] > N_H_1_32) & !no;
        yes |= (self.d[0] > N_H_0_32) & !no;
        yes
    }

    /// Conditionally negate a number, in constant time.
    pub fn cond_negate(&mut self, flag: u32) {
        if !self.is_zero() {
            let mask: u32 = !flag - 1;
            let mut tmp: u64 = ((self.d[0] ^ mask) + ((N_0_32 + 1) & mask)) as u64;
            self.d[0] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += ((self.d[1] ^ mask) + (N_1_32 & mask)) as u64;
            self.d[1] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += ((self.d[2] ^ mask) + (N_2_32 & mask)) as u64;
            self.d[2] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += ((self.d[3] ^ mask) + (N_3_32 & mask)) as u64;
            self.d[3] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += ((self.d[4] ^ mask) + (N_4_32 & mask)) as u64;
            self.d[4] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += ((self.d[5] ^ mask) + (N_5_32 & mask)) as u64;
            self.d[5] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += ((self.d[6] ^ mask) + (N_6_32 & mask)) as u64;
            self.d[6] = (tmp & 0xFFFFFFFF) as u32;
            tmp >>= 32;
            tmp += ((self.d[7] ^ mask) + (N_7_32 & mask)) as u64;
            self.d[7] = (tmp & 0xFFFFFFFF) as u32;
            // return 2 * (mask == 0) - 1;
        }
    }
}

// pub fn muladd(a: &mut u32, b: &mut u32, c0: &mut u32, c1: &mut u32, c2: &mut u32) -> Result<(), String> {
//     let tl: u32;
//     let mut th: u32;
//     let tmp: u64 = (*a * *b) as u64;
//     th = (tmp >> 32) as u32;
//     tl = tmp as u32;
//     *c0 += tl;
//     th += (*c0 < tl) as u32;
//     *c1 += th;
//     *c2 += (*c1 < th) as u32;
//     if *c1 < th || *c2 == 0 {
//         Err(format!("pb"))
//     } else {
//         Ok(())
//     }
// }