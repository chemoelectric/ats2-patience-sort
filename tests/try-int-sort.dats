(*
  Copyright © 2022 Barry Schwartz

  This program is free software: you can redistribute it and/or
  modify it under the terms of the GNU General Public License, as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.

  You should have received copies of the GNU General Public License
  along with this program. If not, see
  <https://www.gnu.org/licenses/>.
*)

#include "share/atspre_staload.hats"
#include "patience-sort/HATS/patience-sort.hats"
staload UN = "prelude/SATS/unsafe.sats"

(*------------------------------------------------------------------*)
(* A simple linear congruential generator.                          *)

(* The multiplier lcg_a comes from Steele, Guy; Vigna, Sebastiano (28
   September 2021). "Computationally easy, spectrally good multipliers
   for congruential pseudorandom number generators".
   arXiv:2001.05304v3 [cs.DS] *)
macdef lcg_a = $UN.cast{uint64} 0xf1357aea2e62a9c5LLU

(* lcg_c must be odd. *)
macdef lcg_c = $UN.cast{uint64} 0xbaceba11beefbeadLLU

var seed : uint64 = $UN.cast 0
val p_seed = addr@ seed

fn
random_double () :<!wrt> double =
  let
    val (pf, fpf | p_seed) = $UN.ptr0_vtake{uint64} p_seed
    val old_seed = ptr_get<uint64> (pf | p_seed)

    (* IEEE "binary64" or "double" has 52 bits of precision. We will
       take the high 48 bits of the seed and divide it by 2**48, to
       get a number 0.0 <= randnum < 1.0 *)
    val high_48_bits = $UN.cast{double} (old_seed >> 16)
    val divisor = $UN.cast{double} (1LLU << 48)
    val randnum = high_48_bits / divisor

    (* The following operation is modulo 2**64, by virtue of standard
       C behavior for uint64_t. *)
    val new_seed = (lcg_a * old_seed) + lcg_c

    val () = ptr_set<uint64> (pf | p_seed, new_seed)
    prval () = fpf pf
  in
    randnum
  end

fn
random_int (m : int, n : int) :<!wrt> int =
  m + $UN.cast{int} (random_double () * (n - m + 1))

(*------------------------------------------------------------------*)

fn {a  : t@ype}
   {tk : tkind}
find_length {n   : int}
            (lst : list (a, n))
    :<> [m : int | m == n] g1uint (tk, m) =
  let
    prval () = lemma_list_param lst
  in
    g1i2u (length lst)
  end

fn
test1 () : void =
  let
    implement
    patience_sort$lt<int> (x, y) =
      x < y

    #define ARRSZ 100

    val example_list =
      $list (22, 15, 98, 82, 22, 4, 58, 70, 80, 38, 49, 48, 46, 54,
             93, 8, 54, 2, 72, 84, 86, 76, 53, 37, 90)

    val sorted_list =
      $list (2, 4, 8, 15, 22, 22, 37, 38, 46, 48, 49, 53, 54, 54, 58,
             70, 72, 76, 80, 82, 84, 86, 90, 93, 98)

    val [n : int] n = find_length example_list
    val () = assertloc (n <= ARRSZ)

    typedef index_t = patience_sort_index_t (uint_kind, n)

    var arr : array (int, ARRSZ)
    val () = array_initize_elt<int> (arr, i2sz ARRSZ, 0)

    var indices : array (index_t, ARRSZ)
    val () = array_initize_elt<index_t> (indices, i2sz ARRSZ, 0u)

    prval @(arr_left, arr_right) =
      array_v_split {int} {..} {ARRSZ} {n} (view@ arr)
    prval @(indices_left, indices_right) =
      array_v_split {index_t} {..} {ARRSZ} {n} (view@ indices)

    prval () = view@ arr := arr_left
    prval () = view@ indices := indices_left

    val () = array_copy_from_list<int> (!(addr@ arr), example_list)
    val () = patience_sort_indices<int> (arr, n, indices)

    prval () = view@ arr := array_v_unsplit (view@ arr, arr_right)
    prval () = view@ indices :=
      array_v_unsplit (view@ indices, indices_right)

    var i : [i : nat | i <= n] uint i
    var p : List (int) = sorted_list
    prval () = lemma_list_param p
  in
    for (i := 0u; i <> n; i := succ i)
      let
        val () = assertloc (isneqz p)
      in
        assertloc (arr[indices[i]] = list_head p);
        p := list_tail p
      end;
    assertloc (iseqz p)
  end

fn
test2 () : void =
  let
    implement
    patience_sort$lt<int> (x, y) =
      x < y

    #define ARRSZ 100

    val example_list =
      $list (22, 15, 98, 82, 22, 4, 58, 70, 80, 38, 49, 48, 46, 54,
             93, 8, 54, 2, 72, 84, 86, 76, 53, 37, 90)

    val sorted_list =
      $list (2, 4, 8, 15, 22, 22, 37, 38, 46, 48, 49, 53, 54, 54, 58,
             70, 72, 76, 80, 82, 84, 86, 90, 93, 98)

    val [n : int] n = find_length example_list
    val () = assertloc (n <= ARRSZ)

    typedef index_t = patience_sort_index_t (uint_kind, n)

    var arr : array (int, ARRSZ)
    val () = array_initize_elt<int> (arr, i2sz ARRSZ, 0)

    prval @(arr_left, arr_right) =
      array_v_split {int} {..} {ARRSZ} {n} (view@ arr)

    prval () = view@ arr := arr_left

    val () = array_copy_from_list<int> (!(addr@ arr), example_list)
    val @(pf_sorted, pfgc_sorted | p_sorted) =
      patience_sort<int> (arr, n)
    macdef sorted = !p_sorted

    prval () = view@ arr := array_v_unsplit (view@ arr, arr_right)

    var i : [i : nat | i <= n] uint i
    var p : List (int) = sorted_list
    prval () = lemma_list_param p
  in
    for (i := 0u; i <> n; i := succ i)
      let
        val () = assertloc (isneqz p)
      in
        assertloc (sorted[i] = list_head p);
        p := list_tail p
      end;
    assertloc (iseqz p);
    array_ptr_free (pf_sorted, pfgc_sorted | p_sorted)
  end

fn
test3 () : void =
  let
    var sz : Size_t
  in
    for (sz := i2sz 0;
         sz <= i2sz 1000000;
         sz := max (i2sz 1, i2sz 10 * sz))
      let
        implement
        patience_sort$lt<int> (x, y) =
          x < y

        implement
        array_quicksort$cmp<int> (x, y) =
          if x < y then
            ~1
          else if x > y then
            1
          else
            0

        implement
        array_initize$init<int> (i, x) =
          x := random_int (1, 1000)

        val @(pf1, pfgc1 | p1) = array_ptr_alloc<int> sz
        val () = array_initize<int> (!p1, sz)

        val @(pf2, pfgc2 | p2) = array_ptr_alloc<int> sz
        val () = array_copy<int> (!p2, !p1, sz)
        val () = array_quicksort<int> (!p2, sz)
        val lst2 = list_vt2t (array2list (!p2, sz))

        val @(pf3, pfgc3 | p3) = patience_sort<int> (!p1, sz)
        val lst3 = list_vt2t (array2list (!p3, sz))
      in
        assertloc (lst2 = lst3);
        array_ptr_free (pf1, pfgc1 | p1);
        array_ptr_free (pf2, pfgc2 | p2);
        array_ptr_free (pf3, pfgc3 | p3)
      end
  end

implement
main0 () =
  begin
    test1 ();
    test2 ();
    test3 ()
  end
