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

/// Returns a sequence of bits from a Scalar32 digit
///
/// Returns an error if count > 32
/// Returns an error if the asked bits come from different digits
///
/// # Arguments
///
/// * `a` - Reference to the Scalar32 to be set
/// * `offset` - Offset of the first bit to count from
/// * `count` - Number of bits to return
pub fn scalar32_get_bits(a: &Scalar32, offset: u32, count: u32) -> Result<u32, &str> {
    if (offset + count - 1) >> 5 == offset >> 5 {
        Ok((a.d[(offset >> 5) as usize] >> (offset & 0x1F)) & ((1 << count) - 1))
    } else {
        Err("error: could not get bits from Scalar32")
    }
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
            0b00001011011011011111111011010111,
            0b11101011011110101010001010101010,
            0b00101010111010100010101100101110,
            0b00010101111010101111100011010111,
            0b11101011011110101010001010101010,
            0b01111011110101011110000001010111,
            0b00001011110101111111111010110111,
            0b11110101000100110110100110101110,
        ];
        let mut scalar: Scalar32 = Scalar32::new(digits);
        // Does the job
        assert_eq!(scalar32_get_bits(&mut scalar, 3, 10).unwrap(), 0b1111011010);
        // Raises error when trying to retrieve bits from two different digits
        assert_eq!(
            scalar32_get_bits(&mut scalar, 26, 10),
            Err("error: could not get bits from Scalar32")
        );
        // Raises error when asking for more than 32 bits
        assert_eq!(
            scalar32_get_bits(&mut scalar, 3, 34),
            Err("error: could not get bits from Scalar32")
        );
    }
}
