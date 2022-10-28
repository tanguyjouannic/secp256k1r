// Limbs of the secp256k1 order
const N_0_32: u32 = 0xD0364141;
const N_1_32: u32 = 0xBFD25E8C;
const N_2_32: u32 = 0xAF48A03B;
const N_3_32: u32 = 0xBAAEDCE6;
const N_4_32: u32 = 0xFFFFFFFE;
const N_5_32: u32 = 0xFFFFFFFF;
const N_6_32: u32 = 0xFFFFFFFF;
const N_7_32: u32 = 0xFFFFFFFF;

// Limbs of 2^256 minus the secp256k1 order
const N_C_0_32: u32 = !N_0_32 + 1;
const N_C_1_32: u32 = !N_1_32;
const N_C_2_32: u32 = !N_2_32;
const N_C_3_32: u32 = !N_3_32;
const N_C_4_32: u32 = 1;

// Limbs of half the secp256k1 order
const N_H_0_32: u32 = 0x681B20A0;
const N_H_1_32: u32 = 0xDFE92F46;
const N_H_2_32: u32 = 0x57A4501D;
const N_H_3_32: u32 = 0x5D576E73;
const N_H_4_32: u32 = 0xFFFFFFFF;
const N_H_5_32: u32 = 0xFFFFFFFF;
const N_H_6_32: u32 = 0xFFFFFFFF;
const N_H_7_32: u32 = 0x7FFFFFFF;

/// A scalar modulo the group order of the secp256k1 curve
///
/// The scalar is made of 8 digits (32bits integers)
#[derive(Copy)]
pub struct Scalar32 {
    d: [u32; 8],
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
    return yes;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scalar32_new() {
        let digits: [u32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let scalar: Scalar32 = Scalar32::new(digits);
        assert_eq!(scalar.d, [0, 1, 2, 3, 4, 5, 6, 7]);
    }

    #[test]
    fn test_scalar32_clear() {
        let digits: [u32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let mut scalar: Scalar32 = Scalar32::new(digits);
        scalar32_clear(&mut scalar);
        assert_eq!(scalar.d, [0, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn test_scalar32_set_int() {
        let digits: [u32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
        let mut scalar: Scalar32 = Scalar32::new(digits);
        let integer: u32 = 32;
        scalar32_set_int(&mut scalar, integer);
        assert_eq!(scalar.d, [32, 0, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn test_scalar32_get_bits() {
        let digits: [u32; 8] = [
            0b11000101101101101111111101101011,
            0b11101011011110101010001010101010,
            0b00101010111010100010101100101110,
            0b00010101111010101111100011010111,
            0b11101011011110101010001010101010,
            0b01111011110101011110000001010111,
            0b00001011110101111111111010110111,
            0b11110101000100110110100110101110,
        ];
        let mut scalar: Scalar32 = Scalar32::new(digits);
        // Tries to get a bit sequence from a single digit
        assert_eq!(
            scalar32_get_bits(&mut scalar, 33, 15).unwrap(),
            0b101000101010101
        );
        // Tries to get a bit sequence from a two different digits
        assert_eq!(scalar32_get_bits(&mut scalar, 60, 8).unwrap(), 0b11101110);
        // Count is 0 : nonsense to get 0 bits
        assert_eq!(
            scalar32_get_bits(&mut scalar, 56, 0),
            Err(String::from("count must be in ]0, 32], got 0"))
        );
        // Count is > 32 : the sequence must fit a 32bits integer
        assert_eq!(
            scalar32_get_bits(&mut scalar, 33, 56),
            Err(String::from("count must be in ]0, 32], got 56"))
        );
        // Overflow : offset + count > 256
        assert_eq!(
            scalar32_get_bits(&mut scalar, 240, 20),
            Err(String::from("offset + count must be in [1, 256], got 260"))
        );
    }

    #[test]
    fn test_scalar32_check_overflow() {
        let digits: [u32; 8] = [
            N_0_32, N_1_32, N_2_32, N_3_32, N_4_32, N_5_32, N_6_32, N_7_32,
        ];
        let limbs: Scalar32 = Scalar32::new(digits);
        // If the scalar is equal to the limbs, should return 1
        assert_eq!(scalar32_check_overflow(&limbs), 1);

        let mut overflowed_scalar = limbs.clone();
        overflowed_scalar.d[0] += 1;
        // If the scalar exceeds the limbs, should return 1
        assert_eq!(scalar32_check_overflow(&overflowed_scalar), 1);

        let mut non_overflowed_scalar = limbs.clone();
        non_overflowed_scalar.d[0] -= 1;
        // If the scalar is less than the limbs, should return 0
        assert_eq!(scalar32_check_overflow(&non_overflowed_scalar), 0);
    }
}
