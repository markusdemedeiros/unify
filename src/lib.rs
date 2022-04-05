#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(unused_imports)]

use either::{Either, Left, Right};

type UnifVar = usize;

struct Language<T> {
    syntax: Vec<TermData<T>>,
}

struct TermData<T> {
    arity: u8,
    data: T,
}

#[derive(Clone, Debug)]
struct TermNode<T> {
    data: T,
    children: Vec<Box<UnifTerm<T>>>,
}

#[derive(Clone, Debug)]
enum UnifTerm<T> {
    Val { value: TermNode<T> },
    Var { value: UnifVar },
}

fn max_unif_vars<T>(t: &UnifTerm<T>) -> usize {
    let mut unchecked: Vec<&UnifTerm<T>> = vec![t];
    let mut max_unif_var: usize = 0;
    loop {
        match unchecked.pop() {
            Some(uterm) => match uterm {
                UnifTerm::Val { value } => {
                    let children = &value.children;
                    for i in 0..(children.len()) {
                        unchecked.push(&*children[i]);
                    }
                }
                UnifTerm::Var { value } => {
                    max_unif_var = std::cmp::max(*value, max_unif_var);
                }
            },
            None => return max_unif_var,
        }
    }
}

/* Left: Representative of a term, explicitly.  */
/* Right: In the equivalence class of it's parent. If it's parent is itself, it's a variable. */

#[derive(Debug)]
struct Substitution<'a, T> {
    indices: Vec<Either<&'a T, usize>>,
}

#[derive(Debug)]
enum SubstitutionError {
    ErrAtomComparison,
    ErrOccursCheck,
}

/*
 *  sigma[x_1 = x_2]...[x_i -> T]... etc
 * TODO: Write a precise semantics for what this should do
 *  A unifying map is slightly more involved than a regular map.
 */
impl<'a, T> Substitution<'a, T> {
    /* Create a new variable substitution
     *  num_vars: size of substitution
     */
    pub fn new(num_vars: usize) -> Self {
        let mut ret = Substitution {
            indices: Vec::with_capacity(num_vars),
        };
        for i in 0..num_vars {
            ret.indices.push(Right(i));
        }
        return ret;
    }

    /*
     * Performs a path-compression search for the parent of a given variable
     */
    fn find_parent(&mut self, n: usize) -> usize {
        let mut r = n;
        let mut stale: Vec<usize> = vec![];

        while let Right(i) = self.indices[r] {
            if i == r {
                break;
            }
            stale.push(r);
            r = i;
        }

        // ASSERTION:
        // self.indices[r] = Left ... || self.indices[r] = Right(r)
        // stale consists of all values on the path to the head, except the head

        for i in stale {
            self.indices[i] = Right(r);
        }

        // ASSERTION:
        // All indices on the path point immediately to their parent

        return r;
    }

    /* Searces for a variable using path compression,
     * Returns either a borrow of a value, or a variable index
     */
    pub fn find(&mut self, n: usize) -> Either<&'a T, usize> {
        let parent = self.find_parent(n);
        return self.indices[parent];
        // TODO: Do I have to duplicate the borrow here? IE does this make sigma
        // forget it owns the borrow to the term?
    }

    /* Searces for a variable using path compression,
     *  Updates the map at the parent, either by assigning a variable to the term
     *  or forgetting the term.
     */
    pub fn binding_set(&mut self, n: usize, term: &'a T) {
        let parent = self.find_parent(n);
        self.indices[parent] = Left(term);
    }

    /*
     * Sets the bindings of x1 and x2 to be the same
     * NOTE: If either x1 or x2's parent have data associated to it, this
     * data will be lost.
     */
    pub fn binding_eq(&mut self, x1: usize, x2: usize) {
        // TODO: It is arbitrary which one we point to which, so
        // you can change this to do union-by-size and improve the
        // runtime to constant.
        // For now, we just pick
        let p1 = self.find_parent(x1);
        let p2 = self.find_parent(x2);
        self.indices[p1] = Right(p2);
    }
}

impl<'a, T> Substitution<'a, TermNode<T>> {
    pub fn lookup(&mut self, u: &'a UnifTerm<T>) -> Either<&'a TermNode<T>, usize> {
        match u {
            UnifTerm::Val { value } => Left(value),
            UnifTerm::Var { value } => self.find(*value - 1),
        }
    }
}

impl<T: Copy> Substitution<'_, TermNode<T>> {
    /*
     * Runs a substitution on a term, perfoming the rewrite and allocating a new experssion
     */
    pub fn rewrite_term(&mut self, t: &UnifTerm<T>) -> UnifTerm<T> {
        // let mut ret = t.clone();
        // let mut stale: Vec<&UnifTerm<T>> = vec![&ret];
        // while let Some(ut) = stale.pop() {
        //     match ut {
        //         UnifTerm::Val { value } => {
        //             for k in &value.children {
        //                 stale.push(k.as_ref());
        //             }
        //         }
        //         UnifTerm::Var { value } => {
        //             match self.find(*value) {
        //                 Left(n) => {
        //                     std::mem::replace(&mut ut, &UnifTerm::Val { value: n.clone() });
        //                 }
        //                 Right(v) => {
        //                     todo!();
        //                 }
        //             }
        //             // *ut = self.
        //         }
        //     }
        // }
        todo!();
    }
}

/*
 * ASSUME: t_1 and t_2 are normalized unification terms
 */
fn unify<'a, T: Eq>(
    t1: &'a UnifTerm<T>,
    t2: &'a UnifTerm<T>,
) -> Result<Substitution<'a, TermNode<T>>, SubstitutionError> {
    let num_vars = std::cmp::max(max_unif_vars(t1), max_unif_vars(t2));
    let mut sigma: Substitution<TermNode<T>> = Substitution::new(num_vars);

    let mut to_unify = vec![(t1, t2)];

    while let Some((ta, tb)) = to_unify.pop() {
        match (sigma.lookup(ta), sigma.lookup(tb)) {
            (Left(na), Left(nb)) => {
                // TODO: Occurs check
                let arity = na.children.len();
                if (na.data != nb.data) | (arity != nb.children.len()) {
                    return Err(SubstitutionError::ErrAtomComparison);
                }
                for i in 0..arity {
                    to_unify.push((&na.children[i], &nb.children[i]));
                }
            }
            (Left(n), Right(x)) | (Right(x), Left(n)) => {
                sigma.binding_set(x, n);
            }
            (Right(x1), Right(x2)) => {
                sigma.binding_eq(x1, x2);
            }
        }
    }

    // Unification complete!
    return Ok(sigma);
}

#[cfg(test)]
mod tests {
    use super::*;

    /* Basic yes/no test to see check if two terms unify or don't */
    fn expect_unify<T: Eq>(t1: &UnifTerm<T>, t2: &UnifTerm<T>, unifies: bool) {
        match unify(t1, t2) {
            Ok(_) => assert!(unifies, "Expected terms to unify"),
            Err(_) => assert!(!unifies, "Expected terms to not unify"),
        }
    }

    #[test]
    fn alphabet_tests() {
        /*
         * ALPHABET LANGAUGE SYNTAX
         *  Char = 'a'..'z'
         *  Var = Char\{a,b,c,d}
         * '1', '2', '3' are metavariables
         *
         * Statics:
         *              1        1  2  3
         * ---  ---  -------- ------------
         *  a    b     c(1)     d(1,2,3)
         *
         * --- z in Var
         *  z
         *
         * A *normalized* alphabet language term
         * has the following:
         *  - All Variables have been turned into UnifVars
         *  - UnifVars are usize
         *  - UnifVars are sequential, starting at 1.
         */
        let alphabet_lang: Language<char> = Language {
            syntax: vec![
                TermData {
                    arity: 0,
                    data: 'a',
                },
                TermData {
                    arity: 0,
                    data: 'b',
                },
                TermData {
                    arity: 1,
                    data: 'c',
                },
                TermData {
                    arity: 3,
                    data: 'd',
                },
            ],
        };

        type ALProgram = UnifTerm<char>;

        let al1: ALProgram = UnifTerm::Var { value: 1 };
        let al2: ALProgram = UnifTerm::Val {
            value: TermNode {
                data: 'a',
                children: vec![],
            },
        };
        let al3: ALProgram = UnifTerm::Val {
            value: TermNode {
                data: 'b',
                children: vec![],
            },
        };
        let al4: ALProgram = UnifTerm::Val {
            value: TermNode {
                data: 'c',
                children: vec![Box::new(UnifTerm::Var { value: 1 })],
            },
        };
        let al5: ALProgram = UnifTerm::Val {
            value: TermNode {
                data: 'd',
                children: vec![
                    Box::new(UnifTerm::Var { value: 1 }),
                    Box::new(UnifTerm::Var { value: 1 }),
                    Box::new(UnifTerm::Var { value: 1 }),
                ],
            },
        };
        let al6: ALProgram = UnifTerm::Val {
            value: TermNode {
                data: 'd',
                children: vec![
                    Box::new(UnifTerm::Var { value: 1 }),
                    Box::new(UnifTerm::Var { value: 2 }),
                    Box::new(UnifTerm::Var { value: 4 }),
                ],
            },
        };

        /* Test: Finding the max of unification variables */
        assert_eq!(max_unif_vars(&al1), 1);
        assert_eq!(max_unif_vars(&al2), 0);
        assert_eq!(max_unif_vars(&al3), 0);
        assert_eq!(max_unif_vars(&al4), 1);
        assert_eq!(max_unif_vars(&al5), 1);
        assert_eq!(max_unif_vars(&al6), 4);

        /* Single variable should unify with everything */
        expect_unify(&al1, &al1, true);
        expect_unify(&al1, &al2, true);
        expect_unify(&al1, &al3, true);
        expect_unify(&al1, &al4, true);
        expect_unify(&al1, &al5, true);
        expect_unify(&al1, &al6, true);

        /* Simple atom comparison should inly unify with itself */
        expect_unify(&al2, &al2, true);
        expect_unify(&al2, &al3, false);
        expect_unify(&al2, &al4, false);
        expect_unify(&al2, &al5, false);
        expect_unify(&al2, &al6, false);

        /* Self-unification for deeper terms */
        expect_unify(&al4, &al4, true);
        expect_unify(&al5, &al5, true);
        expect_unify(&al6, &al6, true);

        /* Unification with differing variables */
        expect_unify(&al5, &al6, true);

        /* Deeper substitutions */
        let al7: ALProgram = UnifTerm::Val {
            value: TermNode {
                data: 'd',
                children: vec![
                    Box::new(UnifTerm::Val {
                        value: (TermNode {
                            data: 'c',
                            children: vec![Box::new(UnifTerm::Var { value: 1 })],
                        }),
                    }),
                    Box::new(UnifTerm::Var { value: 2 }),
                    Box::new(UnifTerm::Var { value: 1 }),
                ],
            },
        };

        let al8: ALProgram = UnifTerm::Val {
            value: TermNode {
                data: 'd',
                children: vec![
                    Box::new(UnifTerm::Var { value: 3 }),
                    Box::new(UnifTerm::Var { value: 1 }),
                    Box::new(UnifTerm::Val {
                        value: (TermNode {
                            data: 'a',
                            children: vec![],
                        }),
                    }),
                ],
            },
        };
        // AL7 = d(c(1), 2, 1)
        // AL8 = d(3, 1, a)
        // MGU should be d(c(a), a, a)
        expect_unify(&al7, &al8, true);

        let al9: ALProgram = UnifTerm::Val {
            value: TermNode {
                data: 'd',
                children: vec![
                    Box::new(UnifTerm::Val {
                        value: (TermNode {
                            data: 'c',
                            children: vec![Box::new(UnifTerm::Var { value: 1 })],
                        }),
                    }),
                    Box::new(UnifTerm::Var { value: 3 }),
                    Box::new(UnifTerm::Var { value: 1 }),
                ],
            },
        };

        // AL9 = d(c(1), 3, 1)
        // AL8 = d(3, 1, a)
        // Should not unify, since c(1) = 3 = 1 = a
        expect_unify(&al9, &al8, false);

        /* Mal-airity terms */

        /* Infinite terms */
    }
}
