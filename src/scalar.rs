// Limbs of the secp256k1 order
pub const N_0_32: u32 = 0xD0364141;
pub const N_1_32: u32 = 0xBFD25E8C;
pub const N_2_32: u32 = 0xAF48A03B;
pub const N_3_32: u32 = 0xBAAEDCE6;
pub const N_4_32: u32 = 0xFFFFFFFE;
pub const N_5_32: u32 = 0xFFFFFFFF;
pub const N_6_32: u32 = 0xFFFFFFFF;
pub const N_7_32: u32 = 0xFFFFFFFF;

// Limbs of 2^256 minus the secp256k1 order
pub const N_C_0_32: u32 = !N_0_32 + 1;
pub const N_C_1_32: u32 = !N_1_32;
pub const N_C_2_32: u32 = !N_2_32;
pub const N_C_3_32: u32 = !N_3_32;
pub const N_C_4_32: u32 = 1;

// Limbs of half the secp256k1 order
pub const N_H_0_32: u32 = 0x681B20A0;
pub const N_H_1_32: u32 = 0xDFE92F46;
pub const N_H_2_32: u32 = 0x57A4501D;
pub const N_H_3_32: u32 = 0x5D576E73;
pub const N_H_4_32: u32 = 0xFFFFFFFF;
pub const N_H_5_32: u32 = 0xFFFFFFFF;
pub const N_H_6_32: u32 = 0xFFFFFFFF;
pub const N_H_7_32: u32 = 0x7FFFFFFF;

/// A scalar modulo the group order of the secp256k1 curve
///
/// The scalar is made of 8 digits (32bits integers)
#[derive(Copy)]
pub struct Scalar32 {
    pub d: [u32; 8],
}

impl Scalar32 {
    /// Returns a Scalar32
    ///
    /// # Arguments
    ///
    /// * `digits` - Array of 8 32bits integers
    pub fn new(digits: [u32; 8]) -> Scalar32 {
        Scalar32 { d: digits }
    }
}

impl Clone for Scalar32 {
    /// Returns a clone of the Scalar32 instance
    fn clone(&self) -> Scalar32 {
        Scalar32 { d: self.d }
    }
}

/// Sets the 8 digits of a Scalar32 to 0
///
/// # Arguments
///
/// * `r` - Mutable reference to the Scalar32 to be reset
pub fn scalar32_clear(r: &mut Scalar32) {
    r.d[0] = 0;
    r.d[1] = 0;
    r.d[2] = 0;
    r.d[3] = 0;
    r.d[4] = 0;
    r.d[5] = 0;
    r.d[6] = 0;
    r.d[7] = 0;
}

/// Sets a Scalar32 to a 32bits integer
///
/// # Arguments
///
/// * `r` - Mutable reference to the Scalar32 to be set
/// * `v` - 32bits integer to set the Scalar32 to
pub fn scalar32_set_int(r: &mut Scalar32, v: u32) {
    r.d[0] = v;
    r.d[1] = 0;
    r.d[2] = 0;
    r.d[3] = 0;
    r.d[4] = 0;
    r.d[5] = 0;
    r.d[6] = 0;
    r.d[7] = 0;
}

/// Returns a sequence of bits from a Scalar32
///
/// The length of this sequence must be able to fill
/// an unsigned 32bits integer.
///
/// # Arguments
///
/// * `a` - Reference to the Scalar32 to be set
/// * `offset` - Offset of the sequence first bit
/// * `count` - Number of bits to return
///
/// # Errors
///
/// Returns a String error if :
/// - count is 0 : nonsense to get 0 bits
/// - count is > 32 : the sequence must fit a 32bits integer
/// - offset + count > 256 : overflow
pub fn scalar32_get_bits(a: &Scalar32, offset: u32, count: u32) -> Result<u32, String> {
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
        Ok((a.d[(offset >> 5) as usize] >> (offset & 0x1F)) & ((1 << count) - 1))
    } else {
        Ok(((a.d[(offset >> 5) as usize] >> (offset & 0x1F))
            | (a.d[((offset >> 5) + 1) as usize] << (32 - (offset & 0x1F))))
            & ((1 << count) - 1))
    }
}

/// Checks if the Scalar32 exceeds or is equal to the
/// limbs of the secp256k1 order
///
/// Returns 1 if the scalar is >= N, else returns 0
///
/// # Arguments
///
/// * `a` - Reference to the Scalar32 to be checked
pub fn scalar32_check_overflow(a: &Scalar32) -> u32 {
    let mut yes: u32 = 0;
    let mut no: u32 = 0;
    no |= (a.d[7] < N_7_32) as u32;
    no |= (a.d[6] < N_6_32) as u32;
    no |= (a.d[5] < N_5_32) as u32;
    no |= (a.d[4] < N_4_32) as u32;
    yes |= ((a.d[4] > N_4_32) as u32) & !no;
    no |= ((a.d[3] < N_3_32) as u32) & !yes;
    yes |= ((a.d[3] > N_3_32) as u32) & !no;
    no |= ((a.d[2] < N_2_32) as u32) & !yes;
    yes |= ((a.d[2] > N_2_32) as u32) & !no;
    no |= ((a.d[1] < N_1_32) as u32) & !yes;
    yes |= ((a.d[1] > N_1_32) as u32) & !no;
    yes |= ((a.d[0] >= N_0_32) as u32) & !no;
    yes
}

/// Reduces the Scalar32 with the provided overflow
///
/// # Arguments
///
/// * `r` - Mutable reference to the Scalar32 to be reduced
/// * `overflow` - Eventual overflow
///
/// # Errors
///
/// Returns a String error if overflow is not in [0, 1]
pub fn scalar32_reduce(r: &mut Scalar32, overflow: u32) -> Result<u32, String> {
    let mut t: u64;
    if overflow > 1 {
        return Err(format!("overflow must be in [0, 1], got {}", overflow));
    }
    t = r.d[0] as u64 + (overflow * N_C_0_32) as u64;
    r.d[0] = t as u32 & 0xFFFFFFFF;
    t >>= 32;
    t += r.d[1] as u64 + (overflow * N_C_1_32) as u64;
    r.d[1] = t as u32 & 0xFFFFFFFF;
    t >>= 32;
    t += r.d[2] as u64 + (overflow * N_C_2_32) as u64;
    r.d[2] = t as u32 & 0xFFFFFFFF;
    t >>= 32;
    t += r.d[3] as u64 + (overflow * N_C_3_32) as u64;
    r.d[3] = t as u32 & 0xFFFFFFFF;
    t >>= 32;
    t += r.d[4] as u64 + (overflow * N_C_4_32) as u64;
    r.d[4] = t as u32 & 0xFFFFFFFF;
    t >>= 32;
    t += r.d[5] as u64;
    r.d[5] = t as u32 & 0xFFFFFFFF;
    t >>= 32;
    t += r.d[6] as u64;
    r.d[6] = t as u32 & 0xFFFFFFFF;
    t >>= 32;
    t += r.d[7] as u64;
    r.d[7] = t as u32 & 0xFFFFFFFF;
    Ok(overflow)
}

/// Adds two Scalar32 together modulo the group order and
/// returns whether it overflowed
///
/// # Arguments
///
/// * `r` - Mutable reference to the Scalar32 that will hold the addition
/// * `a` - Reference to the first Scalar32 member
/// * `b` - Reference to the second Scalar32 member
///
/// # Errors
///
/// Returns a String error if :
/// - the addition generated an overflow that is invalid
/// - the reduction failed
pub fn scalar32_add(r: &mut Scalar32, a: &Scalar32, b: &Scalar32) -> Result<u32, String> {
    let mut t: u64 = (a.d[0] + b.d[0]) as u64;
    r.d[0] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += (a.d[1] + b.d[1]) as u64;
    r.d[1] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += (a.d[2] + b.d[2]) as u64;
    r.d[2] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += (a.d[3] + b.d[3]) as u64;
    r.d[3] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += (a.d[4] + b.d[4]) as u64;
    r.d[4] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += (a.d[5] + b.d[5]) as u64;
    r.d[5] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += (a.d[6] + b.d[6]) as u64;
    r.d[6] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += (a.d[7] + b.d[7]) as u64;
    r.d[7] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    let overflow: u32 = (t + scalar32_check_overflow(r) as u64) as u32;
    if overflow > 1 {
        return Err(format!("expected overflow in [0, 1], got {}", overflow));
    }
    match scalar32_reduce(r, overflow) {
        Ok(overflow) => Ok(overflow),
        Err(e) => Err(format!("failed to reduce with error: {}", e)),
    }
}

/// Conditionally adds a power of two to a scalar
///
/// The result is not allowed to overflow
///
/// # Arguments
///
/// * `r` - Mutable reference to the Scalar32
/// * `bit` - TODO: Explain
/// * `flag` - TODO: Explain
///
/// # Errors
///
/// Returns a String error if :
/// - bit is not in [0, 255]
/// - addition overflowed
pub fn scalar32_cadd_bit(r: &mut Scalar32, mut bit: u32, flag: i32) -> Result<(), String> {
    if bit > 255 {
        return Err(format!("expected bit in [0, 255]")); // TODO: check if 0 is allowed and modify message
    }
    let mut t: u64;
    bit += (flag as u32 - 1) & 0x100;
    t = r.d[0] as u64 + ((((bit >> 5) == 0) as u32) << (bit & 0x1F)) as u64;
    r.d[0] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += r.d[1] as u64 + ((((bit >> 5) == 1) as u32) << (bit & 0x1F)) as u64;
    r.d[1] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += r.d[2] as u64 + ((((bit >> 5) == 2) as u32) << (bit & 0x1F)) as u64;
    r.d[2] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += r.d[3] as u64 + ((((bit >> 5) == 3) as u32) << (bit & 0x1F)) as u64;
    r.d[3] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += r.d[4] as u64 + ((((bit >> 5) == 4) as u32) << (bit & 0x1F)) as u64;
    r.d[4] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += r.d[5] as u64 + ((((bit >> 5) == 5) as u32) << (bit & 0x1F)) as u64;
    r.d[5] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += r.d[6] as u64 + ((((bit >> 5) == 6) as u32) << (bit & 0x1F)) as u64;
    r.d[6] = (t & 0xFFFFFFFF) as u32;
    t >>= 32;
    t += r.d[7] as u64 + ((((bit >> 5) == 7) as u32) << (bit & 0x1F)) as u64;
    r.d[7] = (t & 0xFFFFFFFF) as u32;
    if (t >> 32) != 0 {
        return Err(format!("")); // TODO: Fill the message
    }
    if scalar32_check_overflow(r) != 0 {
        return Err(format!("addition overflowed"));
    }
    Ok(())
}

/// Sets a scalar from a big endian byte array
///
/// The scalar will be reduced modulo group order n
///
/// # Arguments
///
/// * `bin` - Mutable reference to a Scalar32
/// * `b32` - 32 bytes array
/// * `overflow` - non-zero if the scalar overflowed before reduction, zero otherwise
/// 
/// # Errors
/// 
/// Returns a String error if reduction fails
pub fn scalar_set_b32(r: &mut Scalar32, b32: [u8; 32], overflow: &mut u32) -> Result<(), String> {
    r.d[0] =
        b32[31] as u32 | (b32[30] as u32) << 8 | (b32[29] as u32) << 16 | (b32[28] as u32) << 24;
    r.d[1] =
        b32[27] as u32 | (b32[26] as u32) << 8 | (b32[25] as u32) << 16 | (b32[24] as u32) << 24;
    r.d[2] =
        b32[23] as u32 | (b32[22] as u32) << 8 | (b32[21] as u32) << 16 | (b32[20] as u32) << 24;
    r.d[3] =
        b32[19] as u32 | (b32[18] as u32) << 8 | (b32[17] as u32) << 16 | (b32[16] as u32) << 24;
    r.d[4] =
        b32[15] as u32 | (b32[14] as u32) << 8 | (b32[13] as u32) << 16 | (b32[12] as u32) << 24;
    r.d[5] = b32[11] as u32 | (b32[10] as u32) << 8 | (b32[9] as u32) << 16 | (b32[8] as u32) << 24;
    r.d[6] = b32[7] as u32 | (b32[6] as u32) << 8 | (b32[5] as u32) << 16 | (b32[4] as u32) << 24;
    r.d[7] = b32[3] as u32 | (b32[2] as u32) << 8 | (b32[1] as u32) << 16 | (b32[0] as u32) << 24;
    let o: u32 = match scalar32_reduce(r, scalar32_check_overflow(r)) {
        Ok(overflow) => overflow,
        Err(e) => return Err(format!("failed to reduce Scalar32: {}", e)),
    };
    if *overflow != 0 {
        *overflow = o;
    }
    Ok(())
}