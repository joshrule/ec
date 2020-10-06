import unittest
from bin.dsl2lam import beta_normal_form, make_program

class TestEncoding(unittest.TestCase):
    def make_test(self, expr, res):
        self.assertEqual(beta_normal_form(make_program(expr))[0], beta_normal_form(make_program(res))[0])


class TestBoolean(TestEncoding):
    def test_not(self):
        self.make_test('(not true)', 'false')
    def test_if(self):
        self.make_test('(if false true (if true false true))', 'false')
    def test_and_or(self):
        self.make_test('(and true (or true false))', 'true')
        self.make_test('(or (and true false) (and (or true true) false))', 'false')


class TestArithmetic(TestEncoding):

    def test_plus(self):
        self.make_test('(+ (+ 1 3) 2)', '6')
        self.make_test('(+ 0 3)', '3')

    def test_minus(self):
        self.make_test('(- 3 2)', '1')
        self.make_test('(- 3 4)', '0')

    def test_mult(self):
        self.make_test('(* 2 3)', '6')
        self.make_test('(* 3 1)', '(* 1 3)')
        self.make_test('(* 3 0)', '0')

    def test_div(self):
        self.make_test('(/ 5 5)', '1')
        self.make_test('(/ 5 1)', '5')
        self.make_test('(/ 0 5)', '0')
        self.make_test('(/ 8 2)', '4')
        self.make_test('(/ 8 3)', '2')

    def test_compares(self):
        self.make_test('(> 4 5)', 'false')
        self.make_test('(< 1 3)', 'true')
        self.make_test('(== 3 0)', 'false')
        self.make_test('((== 2 2) (< 1 2) (> 1 2))', 'true')

    def test_mod(self):
        self.make_test('(% 8 3)', '2')
        self.make_test('(% 5 1)', '0')
        self.make_test('(% 3 4)', '3')
        self.make_test('(+ (* (/ 15 4) 4) (% 15 4))', '15')
        self.make_test('(is_even 4)', 'true')
        self.make_test('(is_odd (% 6 3))', 'false')


class TestListWithoutIndices(TestEncoding):

    def test_constructor(self):
        self.make_test('(singleton 3)', '(cons 3 [])')
        self.make_test('(range 1 5 2)', '(cons 1 (cons 3 (cons 5 [])))')
        self.make_test('(range 2 6 3)', '(cons 2 (cons 5 []))')
        self.make_test('(repeat 2 4)', '(cons 2 (cons 2 (cons 2 (cons 2 []))))')
        self.make_test('(repeat 3 0)', '[]')

    def test_fold(self):
        self.make_test('(fold - 0 [])', '0')
        self.make_test('(fold - 10 (cons 3 (cons 1 (cons 4 []))))', '2')
        self.make_test('(fold (lambda (lambda (cons $0 $1))) [] (range 1 4 1))', '(range 1 4 1)')

    def test_map(self):
        self.make_test('(map (* 2) (range 1 3 1))', '(cons 2 (cons 4 (cons 6 [])))')
        self.make_test('(map is_even (range 1 3 1))', '(cons false (cons true (cons false [])))')

    def test_filter(self):
        self.make_test('(filter is_even (range 1 4 1))', '(cons 2 (cons 4 []))')

    def test_zip(self):
        self.make_test('(zip (range 1 4 1) (range 1 8 2))',
                       '(cons (cons 1 (cons 1 []))'
                          '(cons (cons 2 (cons 3 []))'
                              '(cons (cons 3 (cons 5 []))'
                                  '(cons (cons 4 (cons 7 [])) []))))')

    def test_append(self):
        self.make_test('(append [] 2)', '(singleton 2)')
        self.make_test('(append (cons 2 (cons 2 [])) 3)', '(cons 2 (cons 2 (cons 3 [])))')

    def test_concat(self):
        self.make_test('(concat (range 1 3 1) (range 4 6 1))', '(range 1 6 1)')

    def test_count(self):
        self.make_test('(count 1 (repeat 1 4))', '4')

    def test_cut_vals(self):
        self.make_test('(cut_vals 0 (cons 1 (cons 0 (cons 2 (cons 3 (cons 0 []))))))', '(range 1 3 1)')

    def test_is_in(self):
        self.make_test('(is_in (range 1 3 1) 2)', 'true')
        self.make_test('(is_in (repeat 1 3) 2)', 'false')

    def test_flatten(self):
        self.make_test('(flatten (repeat (repeat 1 3) 2))', '(repeat 1 6)')

    def test_group(self):
        self.make_test('(group (lambda (% $0 3)) (range 1 5 1))',
                       '(cons (cons 1 (cons 4 [])) (cons (cons 2 (cons 5 [])) (cons (cons 3 []) [])))')

    def test_max(self):
        self.make_test('(max (range 1 4 1))', '4')

    def test_min(self):
        self.make_test('(min (range 3 6 1))', '3')

    def test_product(self):
        self.make_test('(product (range 2 4 1))', '24')

    def test_reverse(self):
        self.make_test('(reverse (range 1 4 1))', '(cons 4 (cons 3 (cons 2 (cons 1 []))))')

    def test_sum(self):
        self.make_test('(sum (range 2 5 1))', '14')

    def test_unique(self):
        self.make_test('(unique (cons 2 (cons 1 (cons 4 (cons 2 [])))))', '(cons 2 (cons 1 (cons 4 [])))')


class TestListWithIndices(TestEncoding):

    def test_first(self):
        self.make_test('(first (cons 3 (cons 2 (cons 4 []))))', '3')
    def test_nth(self):
        self.make_test('(nth 2 (cons 3 (cons 2 (cons 4 []))))', '2')
        self.make_test('(nth 5 (range 2 7 1))', '6')
    def test_second(self):
        self.make_test('(second (cons 3 (cons 2 (cons 4 []))))', '2')
    def test_third(self):
        self.make_test('(third (cons 3 (cons 2 (cons 4 []))))', '4')
    def test_length(self):
        self.make_test('(length (range 2 7 1))', '6')
    def test_last(self):
        self.make_test('(last (range 2 7 1))', '7')

    def test_foldi(self):
        self.make_test('(foldi (lambda (lambda (lambda (+ $1 $2)))) 0 (repeat 1 4))', '10')
    def test_mapi(self):
        self.make_test('(mapi (lambda (lambda (+ $0 $1))) (repeat 2 4))', '(range 3 6 1)')
    def test_filteri(self):
        self.make_test('(filteri (lambda (lambda (is_even $1))) (cons 4 (cons 3 (cons 1 (cons 2 [])))))', '(cons 3 (cons 2 []))')

    def test_insert(self):
        self.make_test('(insert 3 2 (repeat 1 4))', '(cons 1 (cons 3 (cons 1 (cons 1 (cons 1 [])))))')
    def test_replace(self):
        self.make_test('(replace 2 3 (repeat 1 4))', '(cons 1 (cons 3 (cons 1 (cons 1 []))))')
    def test_cut_idx(self):
        self.make_test('(cut_idx 2 (range 2 5 1))', '(cons 2 (cons 4 (cons 5 [])))')
    def test_swap(self):
        self.make_test('(swap 2 3 (range 2 5 1))', '(cons 2 (cons 4 (cons 3 (cons 5 []))))')
    def test_cut_slice(self):
        self.make_test('(cut_slice 3 5 (range 2 6 1))', '(cons 2 (cons 3 []))')
    def test_slice(self):
        self.make_test('(slice 3 5 (range 2 6 1))', '(cons 4 (cons 5 (cons 6 [])))')
    def test_drop(self):
        self.make_test('(drop 2 (range 2 6 1))', '(range 4 6 1)')
    def test_take(self):
        self.make_test('(take 2 (range 2 6 1))', '(range 2 3 1)')
    def test_droplast(self):
        self.make_test('(droplast 2 (range 2 6 1))', '(range 2 4 1)')
    def test_takelast(self):
        self.make_test('(takelast 2 (range 2 6 1))', '(range 5 6 1)')
    def test_splice(self):
        self.make_test('(splice (cons 2 (cons 1 [])) 2 (cons 3 (cons 4 (cons 5 []))))',
                       '(cons 3 (cons 2 (cons 1 (cons 4 (cons 5 [])))))')
        self.make_test('(splice (range 1 3 1) 1 (range 2 4 1))', '(concat (range 1 3 1) (range 2 4 1))')

    def test_find(self):
        self.make_test('(find (lambda (< 3 $0)) (range 2 6 1))', '(range 3 5 1)')
    def test_cut_val(self):
        self.make_test('(cut_val 2 (cons 2 (cons 1 (cons 2 []))))', '(range 1 2 1)')

    def test_sort(self):
        pass
