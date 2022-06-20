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

#define ATS_PACKNAME "ats2-patience-sort"
#define ATS_EXTERN_PREFIX "ats2_patience_sort_"

stadef patience_sort_index_t (n : int, i : int) =
  n == 0 || (0 <= i && i < n)
typedef patience_sort_index_t (tk : tkind, n : int, i : int) =
  [patience_sort_index_t (n, i)]
  g1uint (tk, i)
typedef patience_sort_index_t (tk : tkind, n : int) =
  [i : int]
  patience_sort_index_t (tk, n, i)

(* A type used in intermediate calculations. *)
stadef patience_sort_link_t (n : int, i : int) =
  0 <= i && i <= n
typedef patience_sort_link_t (tk : tkind, n : int, i : int) =
  [patience_sort_link_t (n, i)]
  g1uint (tk, i)
typedef patience_sort_link_t (tk : tkind, n : int) =
  [i : int]
  patience_sort_link_t (tk, n, i)

(* patience_sort$cmp : a strcmp-like function for patience sort. If
                       you want a stable sort, you must use this
                       instead of patience_sort$lt. (I call this kind
                       of sort ‘quasi-stable’, because the stability
                       is not a built-in property of the sorting
                       algorithm.) *)
fn {a : vt@ype}
patience_sort$cmp (x : &RD(a), y : &RD(a)) :<> int

(* patience_sort$lt : an order predicate for patience sort. An
                      implementation of patience_sort$cmp takes
                      precedence over an implementation of
                      patience_sort$lt. *)
fn {a : vt@ype}
patience_sort$lt (x : &RD(a), y : &RD(a)) :<> bool

local

  typedef index_t (tk : tkind, n : int) =
    patience_sort_index_t (tk, n)
  typedef link_t (tk : tkind, n : int) =
    patience_sort_link_t (tk, n)

in

  (* -------------------------------------------------------------- *)
  (* The separate tasks of dealing and merging.                     *)

  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_deal_refparams
            {n           : int}
            {n_workspace : int | 2 * n <= n_workspace}
            (arr         : &RD(array (a, n)),
             n           : g1uint (tk, n),
             piles       : &array (link_t (tk, n)?, n)
                            >> array (link_t (tk, n), n),
             links       : &array (link_t (tk, n)?, n)
                            >> array (link_t (tk, n), n),
             workspace   : &array (link_t (tk, n)?,
                                   n_workspace) >> _)
      :<!wrt> [num_piles : int | num_piles <= n]
              g1uint (tk, num_piles)

  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_deal_valparams
            {n            : int}
            {n_workspace  : int | 2 * n <= n_workspace}
            {p_piles      : addr}
            {p_links      : addr}
            {p_workspace  : addr}
            (pf_piles     : !array_v (link_t (tk, n)?, p_piles, n)
                            >> array_v (link_t (tk, n), p_piles, n),
             pf_links     : !array_v (link_t (tk, n)?, p_links, n)
                            >> array_v (link_t (tk, n), p_links, n),
             pf_workspace : !array_v (link_t (tk, n)?, p_workspace,
                                      n_workspace) >> _ |
             arr          : &RD(array (a, n)),
             n            : g1uint (tk, n),
             p_piles      : ptr p_piles,
             p_links      : ptr p_links,
             p_workspace  : ptr p_workspace)
      :<!wrt> [num_piles : int | num_piles <= n]
              g1uint (tk, num_piles)

  overload patience_sort_deal with patience_sort_deal_refparams
  overload patience_sort_deal with patience_sort_deal_valparams

  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_merge_to_indices_refparams
            {n           : int}
            {num_piles   : pos | num_piles <= n}
            {power       : int | num_piles <= power}
            {n_workspace : int | 4 * power <= n_workspace}
            (pf_exp2     : [exponent : nat] EXP2 (exponent, power) |
             arr         : &RD(array (a, n)),
             n           : g1uint (tk, n),
             num_piles   : g1uint (tk, num_piles),
             power       : g1uint (tk, power),
             piles       : &array (link_t (tk, n), n) >> _,
             links       : &RD(array (link_t (tk, n), n)),
             workspace   : &array (link_t (tk, n)?, n_workspace)
                           >> _,
             sorted      : &array (index_t (tk, n)?, n)
                           >> array (index_t (tk, n), n))
      :<!wrt> void

  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_merge_to_indices_valparams
            {n            : int}
            {num_piles    : pos | num_piles <= n}
            {power        : int | num_piles <= power}
            {n_workspace  : int | 4 * power <= n_workspace}
            {p_piles      : addr}
            {p_links      : addr}
            {p_workspace  : addr}
            (pf_exp2      : [exponent : nat] EXP2 (exponent, power),
             pf_piles     : !array_v (link_t (tk, n), p_piles, n)
                            >> _,
             pf_links     : !array_v (link_t (tk, n), p_links, n)
                            >> _,
             pf_workspace : !array_v (link_t (tk, n)?, p_workspace,
                                      n_workspace) >> _ |
             arr          : &RD(array (a, n)),
             n            : g1uint (tk, n),
             num_piles    : g1uint (tk, num_piles),
             power        : g1uint (tk, power),
             p_piles      : ptr p_piles,
             p_links      : ptr p_links,
             p_workspace  : ptr p_workspace,
             indices      : &array (index_t (tk, n)?, n)
                            >> array (index_t (tk, n), n))
      :<!wrt> void

  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_merge_to_elements_refparams
            {n           : int}
            {num_piles   : pos | num_piles <= n}
            {power       : int | num_piles <= power}
            {n_workspace : int | 4 * power <= n_workspace}
            (pf_exp2     : [exponent : nat] EXP2 (exponent, power) |
             arr         : &array (a, n) >> array (a?!, n),
             n           : g1uint (tk, n),
             num_piles   : g1uint (tk, num_piles),
             power       : g1uint (tk, power),
             piles       : &array (link_t (tk, n), n) >> _,
             links       : &RD(array (link_t (tk, n), n)),
             workspace   : &array (link_t (tk, n)?, n_workspace)
                           >> _,
             elements    : &array (a?, n) >> array (a, n))
      :<!wrt> void

  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_merge_to_elements_valparams
            {n            : int}
            {num_piles    : pos | num_piles <= n}
            {power        : int | num_piles <= power}
            {n_workspace  : int | 4 * power <= n_workspace}
            {p_piles      : addr}
            {p_links      : addr}
            {p_workspace  : addr}
            (pf_exp2      : [exponent : nat] EXP2 (exponent, power),
             pf_piles     : !array_v (link_t (tk, n), p_piles, n)
                            >> _,
             pf_links     : !array_v (link_t (tk, n), p_links, n)
                            >> _,
             pf_workspace : !array_v (link_t (tk, n)?, p_workspace,
                                      n_workspace) >> _ |
             arr          : &array (a, n) >> array (a?!, n),
             n            : g1uint (tk, n),
             num_piles    : g1uint (tk, num_piles),
             power        : g1uint (tk, power),
             p_piles      : ptr p_piles,
             p_links      : ptr p_links,
             p_workspace  : ptr p_workspace,
             elements     : &array (a?, n) >> array (a, n))
      :<!wrt> void

  overload patience_sort_merge_to_indices with
    patience_sort_merge_to_indices_refparams
  overload patience_sort_merge_to_indices with
    patience_sort_merge_to_indices_valparams

  overload patience_sort_merge_to_elements with
    patience_sort_merge_to_elements_refparams of 0
  overload patience_sort_merge_to_elements with
    patience_sort_merge_to_elements_valparams of 0

  (* -------------------------------------------------------------- *)
  (* Doing both deal and merge, to perform a complete act of        *)
  (* sorting. May use stack, malloc, or any combination for the     *)
  (* intermediate work spaces.                                      *)

  (* Fill an array with sorted indices into the original array. Leave
     the original array unaltered. *)
  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_indices
            {n       : int}
            (arr     : &RD(array (a, n)),
             n       : g1uint (tk, n),
             indices : &array (index_t (tk, n)?, n)
                        >> array (index_t (tk, n), n))
      :<!wrt> void

  (* Fill an existing array with the sorted elements. Leave the
     original *data* unaltered, although its *views* may be
     deleted. *)
  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_into_elements_array
            {n        : int}
            (arr      : &array (a, n) >> array (a?!, n),
             n        : g1uint (tk, n),
             elements : &array (a?, n) >> array (a, n))
      :<!wrt> void

  (* Return a new array, of the sorted elements. Leave the original
     *data* unaltered, although its *views* may be deleted. *)
  fn {a  : vt@ype}
     {tk : tkind}
  patience_sort_returning_elements_array
            {n   : int}
            (arr : &array (a, n) >> array (a?!, n),
             n   : g1uint (tk, n))
      :<!wrt> [p : addr]
              @(array_v (a, p, n),
                mfree_gc_v p |
                ptr p)

  overload patience_sort with patience_sort_into_elements_array
  overload patience_sort with patience_sort_returning_elements_array

  (* -------------------------------------------------------------- *)

end
