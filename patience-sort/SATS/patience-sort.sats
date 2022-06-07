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

(* An index into the part of the input array to be sorted. *)
stadef patience_sort_index_t (ifirst : int, len : int, i : int) =
  len == 0 || (ifirst <= i && i < ifirst + len)
typedef patience_sort_index_t (ifirst : int, len : int, i : int) =
  [patience_sort_index_t (ifirst, len, i)] size_t i
typedef patience_sort_index_t (ifirst : int, len : int) =
  [i : int] patience_sort_index_t (ifirst, len, i)

(* A type used in temporary workspaces. *)
stadef patience_sort_link_t (ifirst : int, len : int, i : int) =
  0 <= i && i <= len
typedef patience_sort_link_t (ifirst : int, len : int, i : int) =
  [patience_sort_link_t (ifirst, len, i)] size_t i
typedef patience_sort_link_t (ifirst : int, len : int) =
  [i : int] patience_sort_link_t (ifirst, len, i)

(* patience_sort$lt : the order predicate for patience sort. *)
fn {a : vt@ype}
patience_sort$lt (x : &RD(a), y : &RD(a)) :<> bool

local

  typedef index_t (ifirst : int, len : int) =
    patience_sort_index_t (ifirst, len)
  typedef link_t (ifirst : int, len : int) =
    patience_sort_link_t (ifirst, len)

in

  fn {a : vt@ype}
  patience_sort_given_workspace
            {ifirst, len : int | 0 <= ifirst}
            {n           : int | ifirst + len <= n}
            {power       : int | len <= power}
            {n_workspace : int | (2 * len) + (4 * power)
                                    <= n_workspace}
            (* {n_piles  : int | len <= n_piles} *)
            (* {n_links  : int | len <= n_links} *)
            (* {n_winv   : int | 2 * power <= n_winv} *)
            (* {n_winl   : int | 2 * power <= n_winl} *)
            (pf_exp2     : [exponent : nat] EXP2 (exponent, power) |
             arr         : &RD(array (a, n)),
             ifirst      : size_t ifirst,
             len         : size_t len,
             power       : size_t power,
             workspace   : &array (link_t (ifirst, len)?,
                                   n_workspace) >> _,
             (* piles    : &array (link_t (ifirst, len)?, n_piles) >> _, *)
             (* links    : &array (link_t (ifirst, len)?, n_links) >> _, *)
             (* winvals  : &array (link_t (ifirst, len)?, n_winv) >> _, *)
             (* winlinks : &array (link_t (ifirst, len)?, n_winl) >> _, *)
             sorted      : &array (index_t (ifirst, len)?, len)
                              >> array (index_t (ifirst, len), len))
      :<!wrt> void

  fn {a : vt@ype}
  patience_sort_with_its_own_workspace
            {ifirst, len : int | 0 <= ifirst}
            {n        : int | ifirst + len <= n}
            (arr      : &RD(array (a, n)),
             ifirst   : size_t ifirst,
             len      : size_t len,
             sorted   : &array (index_t (ifirst, len)?, len)
                          >> array (index_t (ifirst, len), len))
      :<!wrt> void

end

overload patience_sort with patience_sort_given_workspace
overload patience_sort with patience_sort_with_its_own_workspace
