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
/// * `scalar` - Mutable reference to the Scalar32 to be reset
pub fn scalar32_clear(scalar: &mut Scalar32) {
    scalar.d[0] = 0;
    scalar.d[1] = 0;
    scalar.d[2] = 0;
    scalar.d[3] = 0;
    scalar.d[4] = 0;
    scalar.d[5] = 0;
    scalar.d[6] = 0;
    scalar.d[7] = 0;
}

/// Sets a Scalar32 to a 32bits integer
///
/// # Arguments
///
/// * `scalar` - Mutable reference to the Scalar32 to be set
/// * `integer` - 32bits integer to set the Scalar32 to
pub fn scalar32_set_int(scalar: &mut Scalar32, integer: u32) {
    scalar.d[0] = integer;
    scalar.d[1] = 0;
    scalar.d[2] = 0;
    scalar.d[3] = 0;
    scalar.d[4] = 0;
    scalar.d[5] = 0;
    scalar.d[6] = 0;
    scalar.d[7] = 0;
}

/// Returns a sequence of bits from a Scalar32
///
/// The length of this sequence must be able to fill
/// an unsigned 32bits integer.
///
/// # Arguments
///
/// * `scalar` - Reference to the Scalar32 to be set
/// * `offset` - Offset of the sequence first bit
/// * `count` - Number of bits to return
///
/// # Errors
///
/// Returns a String error if :
/// - count is 0 : nonsense to get 0 bits
/// - count is > 32 : the sequence must fit a 32bits integer
/// - offset + count > 256 : overflow
pub fn scalar32_get_bits(scalar: &Scalar32, offset: u32, count: u32) -> Result<u32, String> {
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
        Ok((scalar.d[(offset >> 5) as usize] >> (offset & 0x1F)) & ((1 << count) - 1))
    } else {
        Ok(((scalar.d[(offset >> 5) as usize] >> (offset & 0x1F))
            | (scalar.d[((offset >> 5) + 1) as usize] << (32 - (offset & 0x1F))))
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
/// * `scalascalar` - Reference to the Scalar32 to be checked
pub fn scalar32_check_overflow(scalar: &Scalar32) -> u32 {
    let mut yes: u32 = 0;
    let mut no: u32 = 0;
    no |= (scalar.d[7] < N_7_32) as u32;
    no |= (scalar.d[6] < N_6_32) as u32;
    no |= (scalar.d[5] < N_5_32) as u32;
    no |= (scalar.d[4] < N_4_32) as u32;
    yes |= ((scalar.d[4] > N_4_32) as u32) & !no;
    no |= ((scalar.d[3] < N_3_32) as u32) & !yes;
    yes |= ((scalar.d[3] > N_3_32) as u32) & !no;
    no |= ((scalar.d[2] < N_2_32) as u32) & !yes;
    yes |= ((scalar.d[2] > N_2_32) as u32) & !no;
    no |= ((scalar.d[1] < N_1_32) as u32) & !yes;
    yes |= ((scalar.d[1] > N_1_32) as u32) & !no;
    yes |= ((scalar.d[0] >= N_0_32) as u32) & !no;
    yes
}

/// Reduces the Scalar32 modulo group order `n`
///
/// # Arguments
///
/// * `scalar` - Mutable reference to the Scalar32 to be reduced
/// * `overflow` - Eventual overflow
///
/// # Errors
///
/// Returns a String error if overflow is not in [0, 1]
pub fn scalar32_reduce(scalar: &mut Scalar32, overflow: u32) -> Result<u32, String> {
    if overflow > 1 {
        return Err(format!("overflow must be in [0, 1], got {}", overflow));
    }
    let mut tmp: u64;
    tmp = scalar.d[0] as u64 + (overflow * N_C_0_32) as u64;
    scalar.d[0] = tmp as u32 & 0xFFFFFFFF;
    tmp >>= 32;
    tmp += scalar.d[1] as u64 + (overflow * N_C_1_32) as u64;
    scalar.d[1] = tmp as u32 & 0xFFFFFFFF;
    tmp >>= 32;
    tmp += scalar.d[2] as u64 + (overflow * N_C_2_32) as u64;
    scalar.d[2] = tmp as u32 & 0xFFFFFFFF;
    tmp >>= 32;
    tmp += scalar.d[3] as u64 + (overflow * N_C_3_32) as u64;
    scalar.d[3] = tmp as u32 & 0xFFFFFFFF;
    tmp >>= 32;
    tmp += scalar.d[4] as u64 + (overflow * N_C_4_32) as u64;
    scalar.d[4] = tmp as u32 & 0xFFFFFFFF;
    tmp >>= 32;
    tmp += scalar.d[5] as u64;
    scalar.d[5] = tmp as u32 & 0xFFFFFFFF;
    tmp >>= 32;
    tmp += scalar.d[6] as u64;
    scalar.d[6] = tmp as u32 & 0xFFFFFFFF;
    tmp >>= 32;
    tmp += scalar.d[7] as u64;
    scalar.d[7] = tmp as u32 & 0xFFFFFFFF;
    Ok(overflow)
}

/// Adds two Scalar32 together modulo the group order and
/// returns whether it overflowed
///
/// # Arguments
///
/// * `result` - Mutable reference to the Scalar32 that will hold the addition
/// * `a` - Reference to the first Scalar32 member
/// * `b` - Reference to the second Scalar32 member
///
/// # Errors
///
/// Returns a String error if :
/// - the addition generated an overflow that is invalid
/// - the reduction failed
pub fn scalar32_add(result: &mut Scalar32, a: &Scalar32, b: &Scalar32) -> Result<u32, String> {
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
    let overflow: u32 = (tmp + scalar32_check_overflow(result) as u64) as u32;
    if overflow > 1 {
        return Err(format!("expected overflow in [0, 1], got {}", overflow));
    }
    match scalar32_reduce(result, overflow) {
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
/// * `result` - Mutable reference to the Scalar32
/// * `bit` - TODO: Explain
/// * `flag` - TODO: Explain
///
/// # Errors
///
/// Returns a String error if :
/// - bit is not in [0, 255]
/// - addition overflowed
pub fn scalar32_cadd_bit(result: &mut Scalar32, mut bit: u32, flag: i32) -> Result<(), String> {
    if bit > 255 {
        return Err(format!("expected bit in [0, 255]")); // TODO: check if 0 is allowed and modify message
    }
    let mut tmp: u64;
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
        return Err(format!("")); // TODO: Fill the message
    }
    if scalar32_check_overflow(result) != 0 {
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
/// * `scalar` - Mutable reference to a Scalar32
/// * `byte_array` - 32 bytes array
/// * `overflow` - Non-zero if the scalar overflowed before reduction, zero otherwise
///
/// # Errors
///
/// Returns a String error if the reduction fails
pub fn scalar32_set_byte_array(
    scalar: &mut Scalar32,
    byte_array: [u8; 32],
    overflow: &mut u32,
) -> Result<(), String> {
    scalar.d[0] = byte_array[31] as u32
        | (byte_array[30] as u32) << 8
        | (byte_array[29] as u32) << 16
        | (byte_array[28] as u32) << 24;
    scalar.d[1] = byte_array[27] as u32
        | (byte_array[26] as u32) << 8
        | (byte_array[25] as u32) << 16
        | (byte_array[24] as u32) << 24;
    scalar.d[2] = byte_array[23] as u32
        | (byte_array[22] as u32) << 8
        | (byte_array[21] as u32) << 16
        | (byte_array[20] as u32) << 24;
    scalar.d[3] = byte_array[19] as u32
        | (byte_array[18] as u32) << 8
        | (byte_array[17] as u32) << 16
        | (byte_array[16] as u32) << 24;
    scalar.d[4] = byte_array[15] as u32
        | (byte_array[14] as u32) << 8
        | (byte_array[13] as u32) << 16
        | (byte_array[12] as u32) << 24;
    scalar.d[5] = byte_array[11] as u32
        | (byte_array[10] as u32) << 8
        | (byte_array[9] as u32) << 16
        | (byte_array[8] as u32) << 24;
    scalar.d[6] = byte_array[7] as u32
        | (byte_array[6] as u32) << 8
        | (byte_array[5] as u32) << 16
        | (byte_array[4] as u32) << 24;
    scalar.d[7] = byte_array[3] as u32
        | (byte_array[2] as u32) << 8
        | (byte_array[1] as u32) << 16
        | (byte_array[0] as u32) << 24;
    let o: u32 = match scalar32_reduce(scalar, scalar32_check_overflow(scalar)) {
        Ok(overflow) => overflow,
        Err(e) => return Err(format!("failed to reduce Scalar32: {}", e)),
    };
    if *overflow != 0 {
        *overflow = o;
    }
    Ok(())
}

/// Converts a scalar to a byte array
///
/// # Arguments
///
/// * `scalar` - Reference to a Scalar32
/// * `byte_array` - Mutable reference to a 32 bytes array
pub fn scalar32_get_byte_array(scalar: &Scalar32, byte_array: &mut [u8; 32]) {
    byte_array[0] = (scalar.d[7] >> 24) as u8;
    byte_array[1] = (scalar.d[7] >> 16) as u8;
    byte_array[2] = (scalar.d[7] >> 8) as u8;
    byte_array[3] = scalar.d[7] as u8;
    byte_array[4] = (scalar.d[6] >> 24) as u8;
    byte_array[5] = (scalar.d[6] >> 16) as u8;
    byte_array[6] = (scalar.d[6] >> 8) as u8;
    byte_array[7] = scalar.d[6] as u8;
    byte_array[8] = (scalar.d[5] >> 24) as u8;
    byte_array[9] = (scalar.d[5] >> 16) as u8;
    byte_array[10] = (scalar.d[5] >> 8) as u8;
    byte_array[11] = scalar.d[5] as u8;
    byte_array[12] = (scalar.d[4] >> 24) as u8;
    byte_array[13] = (scalar.d[4] >> 16) as u8;
    byte_array[14] = (scalar.d[4] >> 8) as u8;
    byte_array[15] = scalar.d[4] as u8;
    byte_array[16] = (scalar.d[3] >> 24) as u8;
    byte_array[17] = (scalar.d[3] >> 16) as u8;
    byte_array[18] = (scalar.d[3] >> 8) as u8;
    byte_array[19] = scalar.d[3] as u8;
    byte_array[20] = (scalar.d[2] >> 24) as u8;
    byte_array[21] = (scalar.d[2] >> 16) as u8;
    byte_array[22] = (scalar.d[2] >> 8) as u8;
    byte_array[23] = scalar.d[2] as u8;
    byte_array[24] = (scalar.d[1] >> 24) as u8;
    byte_array[25] = (scalar.d[1] >> 16) as u8;
    byte_array[26] = (scalar.d[1] >> 8) as u8;
    byte_array[27] = scalar.d[1] as u8;
    byte_array[28] = (scalar.d[0] >> 24) as u8;
    byte_array[29] = (scalar.d[0] >> 16) as u8;
    byte_array[30] = (scalar.d[0] >> 8) as u8;
    byte_array[31] = scalar.d[0] as u8;
}

/// Checks if a Scalar32 is zero
///
/// Returns true if it is, false otherwise
///
/// # Arguments
///
/// * `scalar` - Reference to the Scalar32 to be checked
pub fn scalar32_is_zero(scalar: &Scalar32) -> bool {
    if (scalar.d[0]
        | scalar.d[1]
        | scalar.d[2]
        | scalar.d[3]
        | scalar.d[4]
        | scalar.d[5]
        | scalar.d[6]
        | scalar.d[7])
        == 0
    {
        true
    } else {
        false
    }
}

/// Computes the complement of a scalar modulo the group order
///
/// # Arguments
///
/// * `scalar` - Reference to the Scalar32 to be negated
/// * `result` - Mutable reference to the Scalar32 to fill with the result
pub fn scalar32_negate(result: &mut Scalar32, scalar: &Scalar32) {
    if scalar32_is_zero(scalar) {
        result.d[0] = 0;
        result.d[1] = 0;
        result.d[2] = 0;
        result.d[3] = 0;
        result.d[4] = 0;
        result.d[5] = 0;
        result.d[6] = 0;
    } else {
        let mut tmp: u64 = !scalar.d[0] as u64 + N_0_32 as u64 + 1;
        result.d[0] = tmp as u32;
        tmp >>= 32;
        tmp += !scalar.d[1] as u64 + N_1_32 as u64;
        result.d[1] = tmp as u32;
        tmp >>= 32;
        tmp += !scalar.d[2] as u64 + N_2_32 as u64;
        result.d[2] = tmp as u32;
        tmp >>= 32;
        tmp += !scalar.d[3] as u64 + N_3_32 as u64;
        result.d[3] = tmp as u32;
        tmp >>= 32;
        tmp += !scalar.d[4] as u64 + N_4_32 as u64;
        result.d[4] = tmp as u32;
        tmp >>= 32;
        tmp += !scalar.d[5] as u64 + N_5_32 as u64;
        result.d[5] = tmp as u32;
        tmp >>= 32;
        tmp += !scalar.d[6] as u64 + N_6_32 as u64;
        result.d[6] = tmp as u32;
        tmp >>= 32;
        tmp += !scalar.d[7] as u64 + N_7_32 as u64;
        result.d[7] = tmp as u32;
    }
}

/// Checks if a Scalar32 is one
///
/// Returns true if it is, false otherwise
///
/// # Arguments
///
/// * `scalar` - Reference to the Scalar32 to be checked
pub fn scalar32_is_one(scalar: &Scalar32) -> bool {
    if ((scalar.d[0] ^ 1)
        | scalar.d[1]
        | scalar.d[2]
        | scalar.d[3]
        | scalar.d[4]
        | scalar.d[5]
        | scalar.d[6]
        | scalar.d[7])
        == 0
    {
        true
    } else {
        false
    }
}
