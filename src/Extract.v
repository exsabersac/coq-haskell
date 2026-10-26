(*
Separate Extraction entrypoint: Require the pieces you care about, then
list identifiers for Coq to emit as Haskell modules.
Depends on Haskell.v for the inductive/constant mappings.

--------
Separate Extraction 入口：Require 所需模块后，列出要抽成 Haskell 的标识符。
归纳类型 / 常量映射依赖 Haskell.v。
*)

Require Import Hask.Prelude.
Require Import Hask.Data.Functor.
Require Import Hask.Data.Functor.Container.
Require Import Hask.Data.Functor.Contravariant.
Require Import Hask.Data.Functor.Identity.
Require Import Hask.Data.Functor.Yoneda.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Applicative.
Require Import Hask.Control.Comonad.
Require Import Hask.Control.Monad.Free.
Require Import Hask.Control.Monad.State.
Require Import Hask.Control.Monad.Trans.Free.
Require Import Hask.Control.Monad.Trans.State.
Require Import Hask.Data.IntMap.
Require Import Hask.Data.IntSet.
Require Import Hask.Data.List.Church.
Require Import Hask.Data.List.
Require Import Hask.Data.Monoid.
Require Import Hask.Data.NonEmpty.
Require Import Hask.Data.Vector.
Require Import Hask.Haskell.

(* Identifiers emitted as .hs modules. / 下列标识符抽成 .hs 模块。 *)
Separate Extraction
  Hask.Control.Applicative.Applicative
  Hask.Control.Monad.Trans.Free.Free
  FreeT
  Hask.Data.Functor.Functor
  Hask.Control.Monad.Monad
  apply
  bind
  (* catMaybes *)
  compose
  concatMapM
  const
  curry
  (* distance *)
  (* emptyIntMap *)
  (* emptyIntSet *)
  (* eqIntMap *)
  (* eqIntSet *)
  (* eq_op *)
  (* exist_in_cons *)
  extend
  (* fin_contra *)
  (* fin_ind *)
  (* fin_rect *)
  first
  flip
  foldM
  (* foldl_with_index *)
  foldrM
  (* foldr_with_index *)
  (* forFold *)
  forFoldM
  (* forFoldr *)
  forFoldrM
  forM
  forM_
  (* fromChurch *)
  get
  (* getBy *)
  getT
  gets
  getsT
  isJust
  iterT
  kleisli_compose
  lebf
  (* lift *)
  liftA2
  liftCoyoneda
  liftF
  liftStateT
  (* list_membership *)
  lowerCoyoneda
  (* map_fst_filter_snd *)
  modify
  modifyT
  (* oddnum *)
  (* oends *)
  (* olast *)
  Maybe_choose
  Maybe_map
  Monoid.Monoid
  mempty
  mappend
  (* partition *)
  put
  putT
  runIdentityF
  (* safe_hd *)
  (* safe_last *)
  second
  (* sumlist *)
  (* toChurch *)
  (* to_from_Church *)
  undefined
  (* vapp *)
  (* vcons *)
  (* vconst *)
  (* vec_ind *)
  (* vec_rect *)
  (* vecn_ind *)
  (* vecn_rect *)
  (* vfoldl *)
  (* vfoldl_with_index *)
  (* vfoldr_with_index *)
  (* vmap *)
  (* vnil *)
  (* vnth *)
  (* vnth_vshiftin *)
  (* vreplace *)
  (* vshiftin *)
  (* vsing *)
  (* vec_to_seq *)
  (* seq_to_vec *).
