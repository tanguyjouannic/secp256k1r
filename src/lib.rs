mod scalar;

// #[cfg(test)]
// mod tests {
//     use crate::scalar::*;

//     #[test]
//     pub fn tt() {
//         let mut a: u32 = 4;
//         let mut b: u32 = 7;
//         let mut c0: u32 = 0;
//         let mut c1: u32 = 0;
//         let mut c2: u32 = 0;
//         muladd(&mut a, &mut b, &mut c0, &mut c1, &mut c2).unwrap();
//         println!("{} {} {}", c0, c1, c2);
//     }
// }

// #[cfg(test)]
// mod tests {
//     use crate::scalar::*;

//     #[test]
//     fn test_scalar32_new() {
//         let digits: [u32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
//         let scalar: Scalar32 = Scalar32::new(digits);
//         assert_eq!(scalar.d, [0, 1, 2, 3, 4, 5, 6, 7]);
//     }

//     #[test]
//     fn test_scalar32_clear() {
//         let digits: [u32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
//         let mut scalar: Scalar32 = Scalar32::new(digits);
//         scalar32_clear(&mut scalar);
//         assert_eq!(scalar.d, [0, 0, 0, 0, 0, 0, 0, 0]);
//     }

//     #[test]
//     fn test_scalar32_set_int() {
//         let digits: [u32; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
//         let mut scalar: Scalar32 = Scalar32::new(digits);
//         let integer: u32 = 32;
//         scalar32_set_int(&mut scalar, integer);
//         assert_eq!(scalar.d, [32, 0, 0, 0, 0, 0, 0, 0]);
//     }

//     #[test]
//     fn test_scalar32_get_bits() {
//         let digits: [u32; 8] = [
//             0b11000101101101101111111101101011,
//             0b11101011011110101010001010101010,
//             0b00101010111010100010101100101110,
//             0b00010101111010101111100011010111,
//             0b11101011011110101010001010101010,
//             0b01111011110101011110000001010111,
//             0b00001011110101111111111010110111,
//             0b11110101000100110110100110101110,
//         ];
//         let mut scalar: Scalar32 = Scalar32::new(digits);
//         // Tries to get a bit sequence from a single digit
//         assert_eq!(
//             scalar32_get_bits(&mut scalar, 33, 15).unwrap(),
//             0b101000101010101
//         );
//         // Tries to get a bit sequence from a two different digits
//         assert_eq!(scalar32_get_bits(&mut scalar, 60, 8).unwrap(), 0b11101110);
//         // Count is 0 : nonsense to get 0 bits
//         assert_eq!(
//             scalar32_get_bits(&mut scalar, 56, 0),
//             Err(String::from("count must be in ]0, 32], got 0"))
//         );
//         // Count is > 32 : the sequence must fit a 32bits integer
//         assert_eq!(
//             scalar32_get_bits(&mut scalar, 33, 56),
//             Err(String::from("count must be in ]0, 32], got 56"))
//         );
//         // Overflow : offset + count > 256
//         assert_eq!(
//             scalar32_get_bits(&mut scalar, 240, 20),
//             Err(String::from("offset + count must be in [1, 256], got 260"))
//         );
//     }

//     #[test]
//     fn test_scalar32_check_overflow() {
//         let digits: [u32; 8] = [
//             N_0_32, N_1_32, N_2_32, N_3_32, N_4_32, N_5_32, N_6_32, N_7_32,
//         ];
//         let limbs: Scalar32 = Scalar32::new(digits);
//         // If the scalar is equal to the limbs, should return 1
//         assert_eq!(scalar32_check_overflow(&limbs), 1);

//         let mut overflowed_scalar = limbs.clone();
//         overflowed_scalar.d[0] += 1;
//         // If the scalar exceeds the limbs, should return 1
//         assert_eq!(scalar32_check_overflow(&overflowed_scalar), 1);

//         let mut non_overflowed_scalar = limbs.clone();
//         non_overflowed_scalar.d[0] -= 1;
//         // If the scalar is less than the limbs, should return 0
//         assert_eq!(scalar32_check_overflow(&non_overflowed_scalar), 0);
//     }
// }
