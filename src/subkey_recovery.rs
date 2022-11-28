/// recovers subkey candidates from known cipher and plaintext of one feistel round
use std::collections::BTreeSet;

use crate::{expand, S, U4, U6};

const INV_P: [usize; 32] = [
    9, 17, 23, 31, 13, 28, 2, 18, 24, 16, 30, 6, 26, 20, 10, 1, 8, 14, 25, 3, 4, 29, 11, 19, 32,
    12, 22, 7, 5, 27, 15, 21,
];

pub fn subkey_candidates(x: u64, y: u64) -> BTreeSet<u64> {
    let l_0 = (x >> 32) as u32;
    let r_0 = x as u32;
    let l_1 = (y >> 32) as u32;
    let r_1 = y as u32;

    let f_output = l_0 ^ r_1;
    let f_pre_permutation = inverse_permutate(f_output);
    let post_expand = expand(r_0);
    let mut s_options: Vec<Vec<U6>> = vec![vec![]; 8];
    for (s, s_options) in s_options.iter_mut().enumerate() {
        let s_input = (f_pre_permutation >> ((7 - s) * 4)) as u8 & 0b1111;
        *s_options = s_box_inputs(s as usize, s_input);
    }

    let mut key_candidates: BTreeSet<u64> = BTreeSet::new();
    for s8 in 0..s_options[7].len() {
        for s7 in 0..s_options[6].len() {
            for s6 in 0..s_options[5].len() {
                for s5 in 0..s_options[4].len() {
                    for s4 in 0..s_options[3].len() {
                        for s3 in 0..s_options[2].len() {
                            for s2 in 0..s_options[1].len() {
                                for s1 in 0..s_options[0].len() {
                                    let mut key =
                                        ((s_options[0][s1 as usize] as u64) << (6 * 7)) as u64;
                                    key += ((s_options[1][s2 as usize] as u64) << (6 * 6)) as u64;
                                    key += ((s_options[2][s3 as usize] as u64) << (6 * 5)) as u64;
                                    key += ((s_options[3][s4 as usize] as u64) << (6 * 4)) as u64;
                                    key += ((s_options[4][s5 as usize] as u64) << (6 * 3)) as u64;
                                    key += ((s_options[5][s6 as usize] as u64) << (6 * 2)) as u64;
                                    key += ((s_options[6][s7 as usize] as u64) << 6) as u64;
                                    key += s_options[7][s8 as usize] as u64;

                                    key_candidates.insert(key ^ post_expand);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    key_candidates
}

fn s_box_inputs(s: usize, output: U4) -> Vec<U6> {
    let mut inputs = vec![];
    for y in 0..4 {
        for x in 0..16 {
            if S[s][y][x] == output {
                let address = ((x as u8) << 1) + (((y as u8) << 4) & 0b100000) + ((y as u8) & 1);
                inputs.push(address);
            }
        }
    }
    inputs
}

bit_map!(inverse_permutate<INV_P>(u32, 32)->u32);

#[cfg(test)]
mod test {
    use super::subkey_candidates;

    #[test]
    fn test1() {
        let x1 = 0xE349EDBF2E8A749D_u64;
        let y1 = 0x2E8A749D4B060F0B_u64;
        let x2 = 0x1349114115611E91_u64;
        let y2 = 0x15611E910296466C_u64;

        let c1 = subkey_candidates(x1, y1);
        let c2 = subkey_candidates(x2, y2);

        let candidate = *c1
            .iter()
            .filter(|x| c2.get(x).is_some())
            .collect::<Vec<&u64>>()[0];

        assert_eq!(candidate, 0x631660191adf);
    }
    #[test]
    fn test2() {
        let x1 = 0x0011223344556677;
        let y1 = 0x4455667764F5C081;
        let x2 = 0xAABBCCDDEEFF0011;
        let y2 = 0xEEFF00116F4588D3;

        let c1 = subkey_candidates(x1, y1);
        let c2 = subkey_candidates(x2, y2);

        let candidate = *c1
            .iter()
            .filter(|x| c2.get(x).is_some())
            .collect::<Vec<&u64>>()[0];

        assert_eq!(candidate, 0x26C5789D1DA1);
    }
    #[test]
    fn test3() {
        let x1 = 0x0123456789ABCDEF;
        let y1 = 0x89ABCDEFFFC71305;
        let x2 = 0xFEDCBA9876543210;
        let y2 = 0x76543210F863C884;

        let c1 = subkey_candidates(x1, y1);
        let c2 = subkey_candidates(x2, y2);

        let candidate = *c1
            .iter()
            .filter(|x| c2.get(x).is_some())
            .collect::<Vec<&u64>>()[0];

        assert_eq!(candidate, 0x7FA9743ED5CE);
    }
}
