//! Composition iterator, binomial and multinomial coefficients.
use formalith::combinatorics::{Combinatorics, CompositionIterator};
use malachite::Integer;

fn compositions(n: usize, k: usize) -> Vec<Vec<usize>> {
    let mut iterator = CompositionIterator::new(n, k);
    let mut res = Vec::new();
    while let Some(composition) = iterator.next_composition() {
        res.push(composition.to_vec());
    }
    res
}

fn binom(n: i64, k: i64) -> Integer {
    Integer::binom(n.into(), k.into())
}

#[test]
fn compositions_are_listed_in_order() {
    assert_eq!(
        compositions(3, 2),
        vec![
            vec![2, 0, 0],
            vec![1, 1, 0],
            vec![1, 0, 1],
            vec![0, 2, 0],
            vec![0, 1, 1],
            vec![0, 0, 2]
        ]
    );
    assert_eq!(
        compositions(2, 3),
        vec![vec![3, 0], vec![2, 1], vec![1, 2], vec![0, 3]]
    );
}

#[test]
fn compositions_edge_cases() {
    assert_eq!(compositions(1, 3), vec![vec![3]]);
    assert_eq!(compositions(2, 0), vec![vec![0, 0]]);
    assert_eq!(compositions(0, 3), Vec::<Vec<usize>>::new());
    assert_eq!(compositions(1, 0), vec![vec![0]]);
}

#[test]
fn compositions_count_and_sum() {
    // There are binom(n+k-1, k) weak compositions of k into n parts
    for n in 1..=5 {
        for k in 0..=5 {
            let all = compositions(n, k);
            assert_eq!(
                Integer::from(all.len()),
                binom((n + k - 1) as i64, k as i64),
                "n={n}, k={k}"
            );
            for composition in &all {
                assert_eq!(composition.len(), n);
                assert_eq!(composition.iter().sum::<usize>(), k);
            }
            let mut dedup = all.clone();
            dedup.sort();
            dedup.dedup();
            assert_eq!(dedup.len(), all.len(), "duplicates for n={n}, k={k}");
        }
    }
}

#[test]
fn binomial() {
    let row: Vec<_> = (0..=6).map(|k| binom(6, k)).collect();
    assert_eq!(row, [1, 6, 15, 20, 15, 6, 1].map(Integer::from));
    assert_eq!(binom(0, 0), 1);
    assert_eq!(binom(1, 0), 1);
    assert_eq!(binom(1, 1), 1);
    assert_eq!(binom(10, 3), 120);
    assert_eq!(binom(50, 25), Integer::from(126_410_606_437_752_u64));
}

#[test]
fn binomial_out_of_range() {
    assert_eq!(binom(5, 7), 0);
    assert_eq!(binom(5, -1), 0);
    assert_eq!(binom(-1, 0), 0);
}

#[test]
fn binomial_pascal_rule() {
    for n in 1..20 {
        for k in 1..n {
            assert_eq!(binom(n, k), binom(n - 1, k - 1) + binom(n - 1, k));
        }
    }
}

#[test]
fn multinomial() {
    let m = |k: &[i64]| Integer::multinom(&k.iter().map(|&x| x.into()).collect::<Vec<_>>());
    assert_eq!(m(&[2, 1, 1]), 12);
    assert_eq!(m(&[]), 1);
    assert_eq!(m(&[3]), 1);
    assert_eq!(m(&[1, 1, 1]), 6);
    assert_eq!(m(&[2, 3]), binom(5, 2));
    assert_eq!(m(&[0, 0, 4]), 1);
}
