//! Knuth Algorithm 7.2.1.1M (_Mixed-radix generation_).

#[allow(dead_code)]
pub fn combinations(n: usize, f: impl FnMut(&[usize])) {
    combinations_mixed(n, &vec![n; n], f)
}

pub fn combinations_mixed(n: usize, r: &[usize], mut f: impl FnMut(&[usize])) {
    let mut a = vec![0; n + 1];
    let mut m = vec![2];
    m.extend(r);
    assert_eq!(a.len(), m.len());

    loop {
        f(&a[1..]);

        let mut j = n;
        while a[j] == m[j] - 1 {
            a[j] = 0;
            j -= 1;
        }

        if j == 0 {
            break;
        }

        a[j] += 1;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn combinations_0() {
        let mut combs = vec![];
        combinations(0, |c| combs.push(c.to_vec()));
        assert_eq!(combs, [[]]);
    }

    #[test]
    fn combinations_1() {
        let mut combs = vec![];
        combinations(1, |c| combs.push(c.to_vec()));
        assert_eq!(combs, [[0]]);
    }

    #[test]
    fn combinations_2() {
        let mut combs = vec![];
        combinations(2, |c| combs.push(c.to_vec()));
        assert_eq!(combs, [[0, 0], [0, 1], [1, 0], [1, 1]]);
    }

    #[test]
    fn combinations_3() {
        let mut combs = vec![];
        combinations(3, |c| combs.push(c.to_vec()));
        assert_eq!(
            combs,
            [
                [0, 0, 0],
                [0, 0, 1],
                [0, 0, 2],
                [0, 1, 0],
                [0, 1, 1],
                [0, 1, 2],
                [0, 2, 0],
                [0, 2, 1],
                [0, 2, 2],
                [1, 0, 0],
                [1, 0, 1],
                [1, 0, 2],
                [1, 1, 0],
                [1, 1, 1],
                [1, 1, 2],
                [1, 2, 0],
                [1, 2, 1],
                [1, 2, 2],
                [2, 0, 0],
                [2, 0, 1],
                [2, 0, 2],
                [2, 1, 0],
                [2, 1, 1],
                [2, 1, 2],
                [2, 2, 0],
                [2, 2, 1],
                [2, 2, 2],
            ]
        );
    }

    #[test]
    fn combinations_3_mixed() {
        let mut combs = vec![];
        combinations_mixed(3, &[1, 2, 3], |c| combs.push(c.to_vec()));
        assert_eq!(
            combs,
            [
                [0, 0, 0],
                [0, 0, 1],
                [0, 0, 2],
                [0, 1, 0],
                [0, 1, 1],
                [0, 1, 2],
            ]
        );
    }
}
