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

staload "patience-sort/SATS/patience-sort.sats"
staload _ = "patience-sort/DATS/patience-sort.dats"

(*

  Currently this is merely an adaptation of the demonstration program
  I wrote for Rosetta Code.

*)

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

(**)
    val example_list =
      $list (22, 15, 98, 82, 22, 4, 58, 70, 80, 38, 49, 48, 46, 54,
             93, 8, 54, 2, 72, 84, 86, 76, 53, 37, 90)

    val sorted_list =
      $list (2, 4, 8, 15, 22, 22, 37, 38, 46, 48, 49, 53, 54, 54, 58,
             70, 72, 76, 80, 82, 84, 86, 90, 93, 98)
(**)
(*
    val example_list = $list (5, 4, 3, 2, 1)
    val sorted_list = $list (1, 2, 3, 4, 5)
*)

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

(**)
    val example_list =
      $list (22, 15, 98, 82, 22, 4, 58, 70, 80, 38, 49, 48, 46, 54,
             93, 8, 54, 2, 72, 84, 86, 76, 53, 37, 90)

    val sorted_list =
      $list (2, 4, 8, 15, 22, 22, 37, 38, 46, 48, 49, 53, 54, 54, 58,
             70, 72, 76, 80, 82, 84, 86, 90, 93, 98)
(**)
(*
    val example_list = $list (5, 4, 3, 2, 1)
    val sorted_list = $list (1, 2, 3, 4, 5)
*)

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

implement
main0 () =
  begin
    test1 ();
    test2 ()
  end
