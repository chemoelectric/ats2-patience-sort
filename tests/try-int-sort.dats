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

implement
main0 () =
  let
    implement
    patience_sort$lt<int> (x, y) =
      x < y

    val example_list =
      $list (22, 15, 98, 82, 22, 4, 58, 70, 80, 38, 49, 48, 46, 54,
             93, 8, 54, 2, 72, 84, 86, 76, 53, 37, 90)

    val sorted_list =
      $list (2, 4, 8, 15, 22, 22, 37, 38, 46, 48, 49, 53, 54, 54, 58,
             70, 72, 76, 80, 82, 84, 86, 90, 93, 98)

    val [len : int] len = find_length example_list

    #define ARRSZ 100
    val () = assertloc (len <= ARRSZ)

    var arr : array (int, ARRSZ)
    val () = array_initize_elt<int> (arr, i2sz ARRSZ, 0)

    prval @(pf_left, pf_right) =
      array_v_split {int} {..} {ARRSZ} {len} (view@ arr)
    val () = array_copy_from_list<int> (!(addr@ arr), example_list)
    prval () = view@ arr := array_v_unsplit (pf_left, pf_right)

    typedef index_t = patience_sort_index_t (uint_kind, len)

    var sorted : array (index_t, ARRSZ)
    val () = array_initize_elt<index_t> (sorted, i2sz ARRSZ, 0u)
    
    prval @(sorted_left, sorted_right) =
      array_v_split {index_t} {..} {ARRSZ} {len} (view@ sorted)
    prval () = view@ sorted := sorted_left

    val () = patience_sort<int> (arr, len, sorted)

    prval () = view@ sorted :=
      array_v_unsplit (view@ sorted, sorted_right)

    var i : [i : nat | i <= len] uint i
    var p : List (int) = sorted_list
    prval () = lemma_list_param p
  in
    for (i := 0u; i <> len; i := succ i)
      let
        val () = assertloc (isneqz p)
      in
        assertloc (arr[sorted[i]] = list_head p);
        p := list_tail p
      end;
    assertloc (iseqz p)
  end
