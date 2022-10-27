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
    /// * `digits` - An array of 8 32bits integers
    pub fn new(digits: [u32; 8]) -> Scalar32 {
        Scalar32 { d: digits }
    }
}

/// Sets de 8 digits of a Scalar32 to 0
/// 
/// # Arguments
///
/// * `r` - The Scalar32 to be reset
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
}
