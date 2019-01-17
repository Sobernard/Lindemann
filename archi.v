(* (c) Copyright 2006-2017 Microsoft Corporation and Inria.                   *)
(* Distributed under the terms of CeCILL-B.                                   *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import ssrint rat algC realalg poly complex.
From mathcomp Require Import polyorder polydiv interval polyrcf mxpoly.
From mathcomp Require Import separable.


(******************************************************************************)
(* This file defines structures for archimedean integral domains and fields   *)
(* equipped with a partial order and a norm.                                  *)
(*                                                                            *)
(*    * ArchiNumDomain (archimedean NumDomain)                                *)
(*  archiNumDomainType == interface for an archimedean num integral domain.   *)
(* ArchiNumDomainType T a                                                     *)
(*                     == packs the archimedean axiom a into an               *)
(*                        archiNumDomainType. The carrier T must have a num   *)
(*                        domain structure.                                   *)
(* [archiNumDomainType of T for S ]                                           *)
(*                     == T-clone of the archiNumDomainType structure of S.   *)
(* [archiNumDomainType of T]                                                  *)
(*                     == clone of a canonical archiNumDomainType structure   *)
(*                        on T.                                               *)
(*                                                                            *)
(*    * ArchiNumField (archimedean NumField)                                  *)
(*   archiNumFieldType == interface for an archimedean num field.             *)
(* ArchiNumFieldType T a                                                      *)
(*                     == packs the archimedean axiom a into an               *)
(*                        archiNumFieldType. The carrier T must have a num    *)
(*                        field structure.                                    *)
(* [archiNumFieldType of T]                                                   *)
(*                     == clone of a canonical archiNumFieldType structure    *)
(*                        on T.                                               *)
(*                                                                            *)
(*    * ArchiNumClosedField (archimedean NumClosedField)                      *)
(* archiNumClosedFieldType                                                    *)
(*                     == interface for an archimedean num closed field.      *)
(* ArchiNumClosedFieldType T a                                                *)
(*                     == packs the archimedean axiom a into an               *)
(*                        archiNumClosedFieldType. The carrier T must have a  *)
(*                        num closed field structure.                         *)
(* [archiNumClosedFieldType of T]                                             *)
(*                     == clone of a canonical archiNumClosedFieldType        *)
(*                        structure on T.                                     *)
(*                                                                            *)
(*    * ArchiRealDomain (archimedean RealDomain)                              *)
(*  archiRealDomainType == interface for an archimedean real integral domain. *)
(* ArchiRealDomainType T a                                                    *)
(*                     == packs the archimedean axiom a into an               *)
(*                        archiRealDomainType. The carrier T must have a real *)
(*                        domain structure.                                   *)
(* [archiRealDomainType of T]                                                 *)
(*                     == clone of a canonical archiRealDomainType structure  *)
(*                        on T.                                               *)
(*                                                                            *)
(*    * ArchiRealField (archimedean RealField)                                *)
(*  archiRealFieldType == interface for an archimedean real field.            *)
(* ArchiRealFieldType T a                                                     *)
(*                     == packs the archimedean axiom a into an               *)
(*                        archiRealFieldType. The carrier T must have a real  *)
(*                        field structure.                                    *)
(* [archiRealFieldType of T]                                                  *)
(*                     == clone of a canonical archiRealFieldType structure   *)
(*                        on T.                                               *)
(*                                                                            *)
(*    * ArchiNumClosedField (archimedean NumClosedField)                      *)
(*        archiRcfType == interface for an archimedean num closed field.      *)
(*    ArchiRcfType T a == packs the archimedean axiom a into an               *)
(*                        archiNumClosedFieldType. The carrier T must have a  *)
(*                        num closed field structure.                         *)
(* [archiRcfType of T] == clone of a canonical archiNumClosedFieldType        *)
(*                        structure on T.                                     *)
(*                                                                            *)
(* NumClosedField structures can be given a total order :                     *)
(* x <=%C y ==                                                                *)
(*                                                                            *)
(*                                                                            *)
(* Over these structures, we have the following operations :                  *)
(*     Cnat == the subset of natural integers.                                *)
(*     Cint == the subset of integers.                                        *)
(* truncC z == for z >= 0, an n : nat s.t. n%:R <= z < n.+1%:R, else 0%N.     *)
(* floorC z == for z \in Num.real, an m : int s.t. m%:~R <= z <= (m + 1)%:~R. *)
(* These are explicitly instanciated for int (Znat), rat (Qnat, Qint) and     *)
(* algC (Cnat, Cint).                                                         *)
(*                                                                            *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Module Archi.

Local Notation num_for T b := (@Num.NumDomain.Pack T b T).

(* Archimedean num structures *)
Module ArchiNumDomain.

Section ClassDef.

Record class_of R := Class {base : Num.NumDomain.class_of R; 
                            _ : @Num.archimedean_axiom (num_for R base)}.
Local Coercion base : class_of >-> Num.NumDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition clone c of phant_id class c := @Pack T c T.
Definition pack b0 (m0 : Num.archimedean_axiom (num_for T b0)) :=
  fun bT b & phant_id (Num.NumDomain.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.NumDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Notation archiNumDomainType := type.
Notation ArchiNumDomainType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'archiNumDomainType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'archiNumDomainType'  'of'  T  'for'  cT ]") 
                                                       : form_scope.
Notation "[ 'archiNumDomainType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'archiNumDomainType'  'of'  T ]") : form_scope.
End Exports.

End ArchiNumDomain.
Import ArchiNumDomain.Exports.

Module ArchiNumField.

Section ClassDef.

Record class_of R := Class { base : Num.NumField.class_of R; 
                             mixin : @Num.archimedean_axiom (num_for R base) }.
Definition base2 R (c : class_of R) := ArchiNumDomain.Class (@mixin R c).
Local Coercion base : class_of >-> Num.NumField.class_of.
Local Coercion base2 : class_of >-> ArchiNumDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack :=
  fun bT b & phant_id (Num.NumField.class bT) (b : Num.NumField.class_of T) =>
  fun mT m & phant_id (ArchiNumDomain.class mT) (@ArchiNumDomain.Class T b m) =>
  Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.
Definition archiNumDomainType := @ArchiNumDomain.Pack cT xclass xT.
Definition fieldType := @GRing.Field.Pack cT xclass xT.
Definition numFieldType := @Num.NumField.Pack cT xclass xT.
Definition join_archiNumDomainType := 
  @ArchiNumDomain.Pack numFieldType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.NumField.class_of.
Coercion base2 : class_of >-> ArchiNumDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Coercion archiNumDomainType : type >-> ArchiNumDomain.type.
Canonical archiNumDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> Num.NumField.type.
Canonical numFieldType.
Canonical join_archiNumDomainType.
Notation archiNumFieldType := type.
Notation "[ 'archiNumFieldType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiNumFieldType'  'of'  T ]") : form_scope.
End Exports.

End ArchiNumField.
Import ArchiNumField.Exports.

Module ArchiNumClosedField.

Section ClassDef.

Record class_of R := Class { base : Num.ClosedField.class_of R; 
                             mixin : @Num.archimedean_axiom (num_for R base) }.
Definition base2 R (c : class_of R) := ArchiNumField.Class (@mixin R c).
Local Coercion base : class_of >-> Num.ClosedField.class_of.
Local Coercion base2 : class_of >-> ArchiNumField.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack :=
  fun bT b & phant_id (Num.ClosedField.class bT)
                      (b : Num.ClosedField.class_of T) =>
  fun mT m & phant_id (ArchiNumDomain.class mT) (@ArchiNumDomain.Class T b m) =>
  Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.
Definition archiNumDomainType := @ArchiNumDomain.Pack cT xclass xT.
Definition fieldType := @GRing.Field.Pack cT xclass xT.
Definition numFieldType := @Num.NumField.Pack cT xclass xT.
Definition archiNumFieldType := @ArchiNumField.Pack cT xclass xT.
Definition closedFieldType := @GRing.ClosedField.Pack cT xclass xT.
Definition numClosedFieldType := @Num.ClosedField.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.ClosedField.class_of.
Coercion base2 : class_of >-> ArchiNumField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Coercion archiNumDomainType : type >-> ArchiNumDomain.type.
Canonical archiNumDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> Num.NumField.type.
Canonical numFieldType.
Coercion archiNumFieldType : type >-> ArchiNumField.type.
Canonical archiNumFieldType.
Coercion closedFieldType : type >-> GRing.ClosedField.type.
Canonical closedFieldType.
Coercion numClosedFieldType : type >-> Num.ClosedField.type.
Canonical numClosedFieldType.
Notation archiNumClosedFieldType := type.
Notation "[ 'archiNumClosedFieldType' 'of' T ]" :=  (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiNumClosedFieldType'  'of'  T ]") : form_scope.
End Exports.

End ArchiNumClosedField.
Import ArchiNumClosedField.Exports.


(* Archimedean real structures *)
Module ArchiRealDomain.

Section ClassDef.

Record class_of R := Class {base : Num.RealDomain.class_of R; 
                            mixin : @Num.archimedean_axiom (num_for R base)}.
Definition base2 R (c : class_of R) := ArchiNumDomain.Class (@mixin R c).
Local Coercion base : class_of >-> Num.RealDomain.class_of.
Local Coercion base2 : class_of >-> ArchiNumDomain.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack :=
  fun bT b & phant_id (Num.RealDomain.class bT) (b : Num.RealDomain.class_of T) 
    =>
  fun mT m & phant_id (ArchiNumDomain.class mT) (@ArchiNumDomain.Class T b m) =>
  Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.
Definition archiNumDomainType := @ArchiNumDomain.Pack cT xclass xT.
Definition realDomainType := @Num.RealDomain.Pack cT xclass xT.
Definition join_archiNumDomainType :=
  @ArchiNumDomain.Pack realDomainType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.RealDomain.class_of.
Coercion base2 : class_of >-> ArchiNumDomain.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Coercion realDomainType : type >-> Num.RealDomain.type.
Canonical realDomainType.
Coercion archiNumDomainType : type >-> ArchiNumDomain.type.
Canonical archiNumDomainType.
Canonical join_archiNumDomainType.
Notation archiRealDomainType := type.
Notation "[ 'archiRealDomainType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiRealDomainType'  'of'  T ]") : form_scope.
End Exports.

End ArchiRealDomain.
Import ArchiRealDomain.Exports.

Module ArchiRealField.

Section ClassDef.

Record class_of R := Class { base : Num.RealField.class_of R; 
                             mixin : @Num.archimedean_axiom (num_for R base) }.
Definition base2 R (c : class_of R) := ArchiNumField.Class (@mixin R c).
Local Coercion base : class_of >-> Num.RealField.class_of.
Definition base3 R (c : class_of R) := @ArchiRealDomain.Class _ c (@mixin _ c). 
Local Coercion base2 : class_of >-> ArchiNumField.class_of.
Local Coercion base3 : class_of >-> ArchiRealDomain.class_of.
Definition base4 R (c : class_of R) := 
  let: Class b m := c in @Num.ArchimedeanField.Class R b m.
Local Coercion base4 : class_of >-> Num.ArchimedeanField.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack :=
  fun bT b & phant_id (Num.RealField.class bT) (b : Num.RealField.class_of T) =>
  fun mT m & phant_id (ArchiNumDomain.class mT) (@ArchiNumDomain.Class T b m) =>
  Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.
Definition realDomainType := @Num.RealDomain.Pack cT xclass xT.
Definition fieldType := @GRing.Field.Pack cT xclass xT.
Definition numFieldType := @Num.NumField.Pack cT xclass xT.
Definition realFieldType := @Num.RealField.Pack cT xclass xT.
Definition archiNumDomainType := @ArchiNumDomain.Pack cT xclass xT.
Definition archiNumFieldType := @ArchiNumField.Pack cT xclass xT.
Definition archiRealDomainType := @ArchiRealDomain.Pack cT xclass xT.
Definition join_archiNumFieldType := @ArchiNumField.Pack numFieldType xclass xT.
Definition join_archiRealDomainType := 
  @ArchiRealDomain.Pack realDomainType xclass xT.
Definition archiFieldType := @Num.ArchimedeanField.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.RealField.class_of.
Coercion base2 : class_of >-> ArchiNumField.class_of.
Coercion base3 : class_of >-> ArchiRealDomain.class_of.
Coercion base4 : class_of >-> Num.ArchimedeanField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Coercion archiNumDomainType : type >-> ArchiNumDomain.type.
Canonical archiNumDomainType.
Coercion realDomainType : type >-> Num.RealDomain.type.
Canonical realDomainType.
Coercion archiRealDomainType : type >-> ArchiRealDomain.type.
Canonical archiRealDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> Num.NumField.type.
Canonical numFieldType.
Coercion archiNumFieldType : type >-> ArchiNumField.type.
Canonical archiNumFieldType.
Coercion realFieldType : type >-> Num.RealField.type.
Canonical realFieldType.
Canonical join_archiNumFieldType.
Canonical join_archiRealDomainType.
Coercion archiFieldType : type >-> Num.ArchimedeanField.type.
Canonical archiFieldType.
Notation archiRealFieldType := type.
Notation "[ 'archiRealFieldType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiRealFieldType'  'of'  T ]") : form_scope.
End Exports.

End ArchiRealField.
Import ArchiRealField.Exports.

Module ArchiRealClosedField.

Section ClassDef.

Record class_of R := Class { base : Num.RealClosedField.class_of R; 
                             mixin : @Num.archimedean_axiom (num_for R base) }.
Definition base2 R (c : class_of R) := ArchiRealField.Class (@mixin R c).
Local Coercion base : class_of >-> Num.RealClosedField.class_of.
Local Coercion base2 : class_of >-> ArchiRealField.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack :=
  fun bT b & phant_id (Num.RealClosedField.class bT) 
                      (b : Num.RealClosedField.class_of T) =>
  fun mT m & phant_id (ArchiNumDomain.class mT) (@ArchiNumDomain.Class T b m) =>
  Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @GRing.Zmodule.Pack cT xclass xT.
Definition ringType := @GRing.Ring.Pack cT xclass xT.
Definition comRingType := @GRing.ComRing.Pack cT xclass xT.
Definition unitRingType := @GRing.UnitRing.Pack cT xclass xT.
Definition comUnitRingType := @GRing.ComUnitRing.Pack cT xclass xT.
Definition idomainType := @GRing.IntegralDomain.Pack cT xclass xT.
Definition numDomainType := @Num.NumDomain.Pack cT xclass xT.
Definition archiNumDomainType := @ArchiNumDomain.Pack cT xclass xT.
Definition realDomainType := @Num.RealDomain.Pack cT xclass xT.
Definition archiRealDomainType := @ArchiRealDomain.Pack cT xclass xT.
Definition fieldType := @GRing.Field.Pack cT xclass xT.
Definition numFieldType := @Num.NumField.Pack cT xclass xT.
Definition archiNumFieldType := @ArchiNumField.Pack cT xclass xT.
Definition realFieldType := @Num.RealField.Pack cT xclass xT.
Definition archiRealFieldType := @ArchiRealField.Pack cT xclass xT.
Definition realClosedFieldType := @Num.RealClosedField.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Num.RealClosedField.class_of.
Coercion base2 : class_of >-> ArchiRealField.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> GRing.Ring.type.
Canonical ringType.
Coercion comRingType : type >-> GRing.ComRing.type.
Canonical comRingType.
Coercion unitRingType : type >-> GRing.UnitRing.type.
Canonical unitRingType.
Coercion comUnitRingType : type >-> GRing.ComUnitRing.type.
Canonical comUnitRingType.
Coercion idomainType : type >-> GRing.IntegralDomain.type.
Canonical idomainType.
Coercion numDomainType : type >-> Num.NumDomain.type.
Canonical numDomainType.
Coercion archiNumDomainType : type >-> ArchiNumDomain.type.
Canonical archiNumDomainType.
Coercion realDomainType : type >-> Num.RealDomain.type.
Canonical realDomainType.
Coercion archiRealDomainType : type >-> ArchiRealDomain.type.
Canonical archiRealDomainType.
Coercion fieldType : type >-> GRing.Field.type.
Canonical fieldType.
Coercion numFieldType : type >-> Num.NumField.type.
Canonical numFieldType.
Coercion realFieldType : type >-> Num.RealField.type.
Canonical realFieldType.
Coercion archiNumFieldType : type >-> ArchiNumField.type.
Canonical archiNumFieldType.
Coercion archiRealFieldType : type >-> ArchiRealField.type.
Canonical archiRealFieldType.
Coercion realClosedFieldType : type >-> Num.RealClosedField.type.
Canonical realClosedFieldType.
Notation archiRcfType := type.
Notation "[ 'archiRcfType' 'of' T ]" :=  (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'archiRcfType'  'of'  T ]") : form_scope.
End Exports.

End ArchiRealClosedField.
Import ArchiRealClosedField.Exports.


Module Import Internals.

Fact archi_bound_subproof (R : archiNumDomainType) : Num.archimedean_axiom R.
Proof. by case: R => ? []. Qed.

End Internals.


Module Import ExtraDef.

Definition archi_bound {R} x := sval (sigW (@archi_bound_subproof R x)).

End ExtraDef.

Notation bound := archi_bound.


Module Theory.


Section ArchiNumTheory.

Variables (R : archiNumDomainType) (x : R).

Lemma archi_boundP : 0 <= x -> x < (bound x)%:R.
Proof. by move/ger0_norm=> {1}<-; rewrite /bound; case: (sigW _). Qed.

End ArchiNumTheory.


Section ArchiRealTheory.

Variables (R : archiRealDomainType) (x : R).

Lemma upper_nthrootP i : (bound x <= i)%N -> x < 2%:R ^+ i.
Proof. 
rewrite /bound; case: (sigW _) => /= b le_x_b le_b_i.
apply: (ler_lt_trans (ler_norm _) (ltr_trans le_x_b _ )).
by rewrite -natrX ltr_nat (leq_ltn_trans le_b_i) // ltn_expl.
Qed.

End ArchiRealTheory.


Section ArchiNumDomainTheory.

Variable R : archiNumDomainType.
Implicit Types (x y z : R) (nu : {rmorphism R -> R}).

(* nat subset *)
Section CnatTheory.

Implicit Types m n : nat.

Fact truncC_subproof x : {m | (0 <= x)-> (m%:R <= x < m.+1%:R) }.
Proof.
have [Rx | _] := boolP (0 <= x); last by exists 0%N.
have /ex_minnP[n lt_x_n1 min_n]: exists n, x < n.+1%:R; last first.
  exists n ; rewrite lt_x_n1 andbT.
  case Dn: n => // [n1]; rewrite -Dn.
  have [//|]:= (real_lerP (rpred_nat _ n) (ger0_real Rx)).
  by rewrite Dn => /min_n; rewrite Dn ltnn.
exists (archi_bound x).
by apply: (ltr_trans (archi_boundP Rx)); rewrite ltr_nat.
Qed.

Definition truncC x := if 0 <= x then sval (truncC_subproof x) else 0%N.
Definition Cnat := Qualifier 1 (fun x : R => (truncC x)%:R == x).

Fact Cnat_key : pred_key Cnat. Proof. by []. Qed.
Canonical Cnat_keyed := KeyedQualifier Cnat_key.

Lemma truncC_itv x : 0 <= x -> (truncC x)%:R <= x < (truncC x).+1%:R.
Proof.
move => x_ge0; rewrite /truncC ifT //.
by case: (truncC_subproof x) => /= m; move/(_ x_ge0).
Qed.

Lemma truncC_def x n : n%:R <= x < n.+1%:R -> truncC x = n.
Proof.
case/andP=> lemx ltxm1; apply/eqP; rewrite eqn_leq -ltnS -[(n <= _)%N]ltnS.
have /truncC_itv/andP[lefx ltxf1]: x >= 0.
  by apply: (ler_trans _ lemx); apply: ler0n.
by rewrite -!(ltr_nat R) 2?(@ler_lt_trans _ x).
Qed.

Lemma natCK : cancel (GRing.natmul 1) truncC.
Proof. by move=> m; apply: truncC_def; rewrite ler_nat ltr_nat ltnS leqnn. Qed.

Lemma truncCK : {in Cnat, cancel truncC (GRing.natmul 1)}.
Proof. by move=> x /eqP. Qed.

Lemma truncC0 : truncC 0 = 0%N. Proof. exact: (natCK 0%N). Qed.
Lemma truncC1 : truncC 1 = 1%N. Proof. exact: (natCK 1%N). Qed.
Hint Resolve truncC0 truncC1.

Lemma CnatP x : reflect (exists n, x = n%:R) (x \is a Cnat).
Proof.
by apply: (iffP eqP) => [<- | [n ->]]; [exists (truncC x) | rewrite natCK].
Qed.

Lemma Cnat_nat n : n%:R \is a Cnat. Proof. by apply/CnatP; exists n. Qed.
Hint Resolve Cnat_nat.

Lemma truncCD :
  {in Cnat & Num.nneg, {morph truncC : x y / x + y >-> (x + y)%N}}.
Proof.
move=> _ y /CnatP[n ->] y_ge0; apply: truncC_def.
by rewrite -addnS !natrD !natCK ler_add2l ltr_add2l truncC_itv.
Qed.

Lemma truncCM : {in Cnat &, {morph truncC : x y / x * y >-> (x * y)%N}}.
Proof. by move=> _ _ /CnatP[n1 ->] /CnatP[n2 ->]; rewrite -natrM !natCK. Qed.

Lemma truncCX n : {in Cnat, {morph truncC : x / x ^+ n >-> (x ^ n)%N}}.
Proof. by move=> _ /CnatP[n1 ->]; rewrite -natrX !natCK. Qed.

Lemma rpred_Cnat S (ringS : semiringPred S) (kS : keyed_pred ringS) x :
  x \is a Cnat -> x \in kS.
Proof. by case/CnatP=> n ->; apply: rpred_nat. Qed.

Lemma Cnat0 : 0 \is a Cnat. Proof. exact: (Cnat_nat 0). Qed.
Lemma Cnat1 : 1 \is a Cnat. Proof. exact: (Cnat_nat 1). Qed.
Hint Resolve Cnat0 Cnat1.

Fact Cnat_semiring : semiring_closed Cnat.
Proof.
by do 2![split] => //= _ _ /CnatP[n ->] /CnatP[m ->]; rewrite -(natrD, natrM).
Qed.
Canonical Cnat_addrPred := AddrPred Cnat_semiring.
Canonical Cnat_mulrPred := MulrPred Cnat_semiring.
Canonical Cnat_semiringPred := SemiringPred Cnat_semiring.

Lemma real_Cnat : {subset Cnat <= Num.real}.
Proof. move=> _ /CnatP[m ->]; apply: realn. Qed.

Lemma Cnat_normK x : x \is a Cnat -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/real_Cnat/real_normK. Qed.

Lemma truncC_gt0 x : (0 < truncC x)%N = (1 <= x).
Proof.
apply/idP/idP=> [m_gt0 | x_ge1].
  have /truncC_itv/andP[lemx _]: 0 <= x.
    by move: m_gt0; rewrite /truncC; case: ifP.
  by apply: ler_trans lemx; rewrite ler1n.
have /truncC_itv/andP[_ ltxm1]:= ler_trans ler01 x_ge1.
by rewrite -ltnS -(ltr_nat R) (ler_lt_trans x_ge1).
Qed.

Lemma truncC0Pn x : reflect (truncC x = 0%N) (~~ (1 <= x)).
Proof. by rewrite -truncC_gt0 -eqn0Ngt; apply: eqP. Qed.

Lemma Cnat_ge0 x : x \is a Cnat -> 0 <= x.
Proof. by case/CnatP=> n ->; apply: ler0n. Qed.

Lemma Cnat_gt0 x : x \is a Cnat -> (0 < x) = (x != 0).
Proof. by case/CnatP=> n ->; rewrite pnatr_eq0 ltr0n lt0n. Qed.

Lemma norm_Cnat x : x \is a Cnat -> `|x| = x.
Proof. by move/Cnat_ge0/ger0_norm. Qed.

Lemma Cnat_sum_eq1 (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> F i \is a Cnat) -> \sum_(i | P i) F i = 1 ->
   {i : I | [/\ P i, F i = 1 & forall j, j != i -> P j -> F j = 0]}.
Proof.
move=> natF sumF1; pose nF i := truncC (F i).
have{natF} defF i: P i -> F i = (nF i)%:R by move/natF/eqP.
have{sumF1} /eqP sumF1: (\sum_(i | P i) nF i == 1)%N.
  by rewrite -(@eqr_nat R) natr_sum -(eq_bigr _ defF) sumF1.
have [i Pi nZfi]: {i : I | P i & nF i != 0%N}.
  by apply/sig2W/exists_inP; rewrite -negb_forall_in -sum_nat_eq0 sumF1.
have F'ge0 := (leq0n _, etrans (eq_sym _ _) (sum_nat_eq0 (predD1 P i) nF)).
rewrite -lt0n in nZfi; have [_] := (leqif_add (leqif_eq nZfi) (F'ge0 _)).
rewrite /= big_andbC -bigD1 // sumF1 => /esym/andP/=[/eqP Fi1 /forall_inP Fi'0].
exists i; split=> // [|j neq_ji Pj]; first by rewrite defF // -Fi1.
by rewrite defF // (eqP (Fi'0 j _)) // neq_ji.
Qed.

Lemma Cnat_mul_eq1 x y :
  x \is a Cnat -> y \is a Cnat -> (x * y == 1) = (x == 1) && (y == 1).
Proof. by do 2!move/truncCK <-; rewrite -natrM !pnatr_eq1 muln_eq1. Qed.

Lemma Cnat_prod_eq1 (I : finType) (P : pred I) (F : I -> R) :
    (forall i, P i -> F i \is a Cnat) -> \prod_(i | P i) F i = 1 ->
  forall i, P i -> F i = 1.
Proof.
move=> natF prodF1; apply/eqfun_inP; rewrite -big_andE.
move: prodF1; elim/(big_load (fun x => x \is a Cnat)): _.
elim/big_rec2: _ => // i all1x x /natF N_Fi [Nx x1all1].
by split=> [|/eqP]; rewrite ?rpredM ?Cnat_mul_eq1 // => /andP[-> /eqP].
Qed.

(* predCmod *)
Variables (U V : lmodType R) (f : {additive U -> V}).

Lemma raddfZ_Cnat a u : a \is a Cnat -> f (a *: u) = a *: f u. 
Proof. by case/CnatP=> n ->; apply: raddfZnat. Qed.

Lemma rpredZ_Cnat S (addS : @addrPred V S) (kS : keyed_pred addS) :
  {in Cnat & kS, forall z u, z *: u \in kS}.
Proof. by move=> _ u /CnatP[n ->]; apply: rpredZnat. Qed.

(* autC *)
Lemma aut_Cnat nu : {in Cnat, nu =1 id}.
Proof. by move=> _ /CnatP[n ->]; apply: rmorph_nat. Qed.

End CnatTheory.

(* int subset *)
Section CintTheory.

Implicit Types m : int.

Fact floorC_subproof x : {m | x \is Num.real -> intr m <= x < intr (m + 1)}.
Proof.
have [Rx | _] := boolP (x \is Num.real); last by exists 0.
without loss x_ge0: x Rx / x >= 0.
  have [x_ge0 | /ltrW x_le0] := real_ger0P Rx; first exact.
  case/(_ (- x)) => [||m /(_ isT)]; rewrite ?rpredN ?oppr_ge0 //.
  rewrite ler_oppr ltr_oppl -!rmorphN opprD /= ltr_neqAle ler_eqVlt.
  case: eqP => [-> _ | _ /and3P[lt_x_m _ le_m_x]].
    by exists (- m) => _; rewrite lerr rmorphD ltr_addl ltr01.
  by exists (- m - 1); rewrite le_m_x subrK.
exists (Posz (truncC x)) => _ ; rewrite addrC -intS -!natz !mulrz_nat.
exact: (truncC_itv x_ge0).
Qed.

Definition floorC x := sval (floorC_subproof x).
Definition Cint := [qualify a x : R | (floorC x)%:~R == x].

Fact Cint_key : pred_key Cint. Proof. by []. Qed.
Canonical Cint_keyed := KeyedQualifier Cint_key.

Lemma floorC_itv x : x \is Num.real -> (floorC x)%:~R <= x < (floorC x + 1)%:~R.
Proof. by rewrite /floorC => Rx; case: (floorC_subproof x) => //= m; apply. Qed.

Lemma floorC_def x m : m%:~R <= x < (m + 1)%:~R -> floorC x = m.
Proof.
case/andP=> lemx ltxm1; apply/eqP; rewrite eqr_le -!ltz_addr1.
have /floorC_itv/andP[lefx ltxf1]: x \is Num.real.
  by rewrite -[x](subrK m%:~R) rpredD ?realz ?ler_sub_real.
by rewrite -!(ltr_int R) 2?(@ler_lt_trans _ x).
Qed.

Lemma intCK : cancel intr floorC.
Proof.
by move=> m; apply: floorC_def; rewrite ler_int ltr_int ltz_addr1 lerr.
Qed.

Lemma floorCK : {in Cint, cancel floorC intr}. Proof. by move=> z /eqP. Qed.

Lemma floorC0 : floorC 0 = 0. Proof. exact: (intCK 0). Qed.
Lemma floorC1 : floorC 1 = 1. Proof. exact: (intCK 1). Qed.
Hint Resolve floorC0 floorC1.

Lemma floorCpK (p : {poly R}) :
  p \is a polyOver Cint -> map_poly intr (map_poly floorC p) = p.
Proof.
move/(all_nthP 0)=> Zp; apply/polyP=> i.
rewrite coef_map coef_map_id0 //= -[p]coefK coef_poly.
by case: ifP => [/Zp/floorCK // | _]; rewrite floorC0.
Qed.

Lemma floorCpP (p : {poly R}) :
  p \is a polyOver Cint -> {q | p = map_poly intr q}.
Proof. by exists (map_poly floorC p); rewrite floorCpK. Qed.

Lemma Cint_int m : m%:~R \is a Cint.
Proof. by rewrite unfold_in intCK. Qed.

Lemma CintP x : reflect (exists m, x = m%:~R) (x \is a Cint).
Proof.
by apply: (iffP idP) => [/eqP<-|[m ->]]; [exists (floorC x) | apply: Cint_int].
Qed.

Lemma floorCD : {in Cint & Num.real, {morph floorC : x y / x + y}}.
Proof.
move=> _ y /CintP[m ->] Ry; apply: floorC_def.
by rewrite -addrA 2!rmorphD /= intCK ler_add2l ltr_add2l floorC_itv.
Qed.

Lemma floorCN : {in Cint, {morph floorC : x / - x}}.
Proof. by move=> _ /CintP[m ->]; rewrite -rmorphN !intCK. Qed.

Lemma floorCM : {in Cint &, {morph floorC : x y / x * y}}.
Proof. by move=> _ _ /CintP[m1 ->] /CintP[m2 ->]; rewrite -rmorphM !intCK. Qed.

Lemma floorCX n : {in Cint, {morph floorC : x / x ^+ n}}.
Proof. by move=> _ /CintP[m ->]; rewrite -rmorphX !intCK. Qed.

Lemma rpred_Cint S (ringS : subringPred S) (kS : keyed_pred ringS) x :
  x \is a Cint -> x \in kS.
Proof. by case/CintP=> m ->; apply: rpred_int. Qed.

Lemma Cint0 : 0 \is a Cint. Proof. exact: (Cint_int 0). Qed.
Lemma Cint1 : 1 \is a Cint. Proof. exact: (Cint_int 1). Qed.
Hint Resolve Cint0 Cint1.

Fact Cint_subring : subring_closed Cint.
Proof.
by split=> // _ _ /CintP[m ->] /CintP[p ->];
    rewrite -(rmorphB, rmorphM) Cint_int.
Qed.
Canonical Cint_opprPred := OpprPred Cint_subring.
Canonical Cint_addrPred := AddrPred Cint_subring.
Canonical Cint_mulrPred := MulrPred Cint_subring.
Canonical Cint_zmodPred := ZmodPred Cint_subring.
Canonical Cint_semiringPred := SemiringPred Cint_subring.
Canonical Cint_smulrPred := SmulrPred Cint_subring.
Canonical Cint_subringPred := SubringPred Cint_subring.

Lemma Creal_Cint : {subset Cint <= Num.real}.
Proof. by move=> _ /CintP[m ->]; apply: realz. Qed.

Lemma Cint_normK x : x \is a Cint -> `|x| ^+ 2 = x ^+ 2.
Proof. by move/Creal_Cint/real_normK. Qed.

Lemma CintEsign x : x \is a Cint -> x = (-1) ^+ (x < 0)%R * `|x|.
Proof. by move/Creal_Cint/realEsign. Qed.

(* relation between Cint and Cnat. *)
Lemma Cint_Cnat : {subset Cnat <= Cint}.
Proof. by move=> _ /CnatP[n ->]; rewrite pmulrn Cint_int. Qed.

Lemma CintE x : (x \is a Cint) = (x \is a Cnat) || (- x \is a Cnat).
Proof.
apply/idP/idP=> [/CintP[[n | n] ->] | ]; first by rewrite Cnat_nat.
  by rewrite NegzE opprK Cnat_nat orbT.
by case/pred2P=> [<- | /(canLR (@opprK _)) <-]; rewrite ?rpredN rpred_nat.
Qed.

Lemma Cnat_norm_Cint x : x \is a Cint -> `|x| \is a Cnat.
Proof.
case/CintP=> [m ->]; rewrite [m]intEsign rmorphM rmorph_sign.
by rewrite normrM normr_sign mul1r normr_nat rpred_nat.
Qed.

Lemma CnatEint x : (x \is a Cnat) = (x \is a Cint) && (0 <= x).
Proof.
apply/idP/andP=> [Nx | [Zx x_ge0]]; first by rewrite Cint_Cnat ?Cnat_ge0.
by rewrite -(ger0_norm x_ge0) Cnat_norm_Cint.
Qed.

Lemma CintEge0 x : 0 <= x -> (x \is a Cint) = (x \is a Cnat).
Proof. by rewrite CnatEint andbC => ->. Qed.

Lemma Cnat_exp_even x n : ~~ odd n -> x \is a Cint -> x ^+ n \is a Cnat.
Proof.
move=> n_oddF x_Cint; rewrite CnatEint; apply/andP; split.
  by apply: (rpredX _ x_Cint).
by apply: (real_exprn_even_ge0 (Creal_Cint x_Cint) n_oddF).
Qed.

Lemma norm_Cint_ge1 x : x \is a Cint -> x != 0 -> 1 <= `|x|.
Proof.
rewrite -normr_eq0 => /Cnat_norm_Cint/CnatP[n ->].
by rewrite pnatr_eq0 ler1n lt0n.
Qed.

Lemma sqr_Cint_ge1 x : x \is a Cint -> x != 0 -> 1 <= x ^+ 2.
Proof.
by move=> Zx nz_x; rewrite -Cint_normK // expr_ge1 ?normr_ge0 ?norm_Cint_ge1.
Qed.

Lemma Cint_ler_sqr x : x \is a Cint -> x <= x ^+ 2.
Proof.
move=> Zx; have [-> | nz_x] := eqVneq x 0; first by rewrite expr0n.
apply: ler_trans (_ : `|x| <= _); first by rewrite real_ler_norm ?Creal_Cint.
by rewrite -Cint_normK // ler_eexpr // norm_Cint_ge1.
Qed.

(* relation between truncC and oldtruncC. *)
Lemma truncC_old x : (truncC x = if (0 <= x) then `|floorC x|%N else 0%N).
Proof.
case: ifP => [x_ge0 | x_ge0F]; last by rewrite /truncC; apply: ifF.
have /andP [fl_ler lt_fl] : (`|floorC x|%N)%:R <= x < (`|floorC x|%N).+1%:R.
  have /andP[lemx ltxm1] := floorC_itv (ger0_real x_ge0).
  rewrite -addn1 !pmulrn PoszD gez0_abs ?lemx //.
  by rewrite -ltz_addr1 -(ltr_int R) (ler_lt_trans x_ge0).
have /andP [tr_ler lt_tr] := (truncC_itv x_ge0).
apply/eqP; rewrite eqn_leq; apply/andP.
do 2?[rewrite -ltnS -(ltr_nat R)]; split.
  by apply: (ler_lt_trans tr_ler lt_fl).
by apply: (ler_lt_trans fl_ler lt_tr).
Qed.

(* predCmod *)
Variables (U V : lmodType R) (f : {additive U -> V}).

Lemma raddfZ_Cint a u : a \is a Cint -> f (a *: u) = a *: f u. 
Proof. by case/CintP=> m ->; rewrite !scaler_int raddfMz. Qed.

Lemma rpredZ_Cint S (subS : @zmodPred V S) (kS : keyed_pred subS) :
  {in Cint & kS, forall z u, z *: u \in kS}.
Proof. by move=> _ u /CintP[m ->]; apply: rpredZint. Qed.

(* autC *)
Lemma aut_Cint nu : {in Cint, nu =1 id}.
Proof. by move=> _ /CintP[m ->]; apply: rmorph_int. Qed.

End CintTheory.

End ArchiNumDomainTheory.

Arguments Cnat [R].
Arguments Cint [R].
Arguments natCK [R].
Arguments truncC [R].
Hint Resolve truncC0 truncC1 Cnat_nat Cnat0 Cnat1.
Hint Resolve floorC0 floorC1 Cint_int Cint0 Cint1 Cint_Cnat.

Section ArchiNumFieldTheory.

Variable R : archiNumFieldType.

Implicit Type nu : {rmorphism R -> R}.

Lemma Cnat_aut nu x : (nu x \is a Cnat) = (x \is a Cnat).
Proof.
by do [apply/idP/idP=> Nx; have:= aut_Cnat nu Nx] => [/fmorph_inj <- | ->].
Qed.

Lemma Cint_aut nu x : (nu x \is a Cint) = (x \is a Cint).
Proof. by rewrite !CintE -rmorphN !Cnat_aut. Qed.

End ArchiNumFieldTheory.

Section ArchiNumClosedFieldTheory.

Variable R : archiNumClosedFieldType.

Implicit Type x y : R.

Lemma conj_Cnat x : x \is a Cnat -> x^* = x.
Proof. by case/CnatP=> n ->; apply: rmorph_nat. Qed.

Lemma conj_Cint x : x \is a Cint -> x^* = x.
Proof. by move/Creal_Cint/conj_Creal. Qed.

End ArchiNumClosedFieldTheory.

Section ArchiRealFieldTheory.

Variable R : archiRealFieldType.

Lemma rat_dense (x y : R) :
  x < y -> {q : rat | x < ratr q < y}.
Proof.
move=> lt_xy; pose e := y - x.
have lt_e0 : 0 < e :> R by rewrite subr_gt0.
have lt_eI0 := (divr_ge0 ler01 (ltrW lt_e0)).
have := (archi_boundP lt_eI0); set n := bound _ => lt_n; have := lt_n.
have lt_n0 : 0 < n%:R :> R by apply: (ler_lt_trans lt_eI0 lt_n).
rewrite (ltr_pdivr_mulr _ 1 lt_e0) mulrC -(ltr_pdivr_mulr _ _ lt_n0) => lt_e.
have /floorC_itv/andP[] : x * n%:R \is Num.real by apply: num_real.
set m := floorC _; rewrite -(ler_pdivr_mulr _ _ lt_n0) => le_rx.
rewrite -(ltr_pdivl_mulr _ _ lt_n0) => lt_xr; pose r := (m + 1)%:Q / n%:Q.
exists r; rewrite fmorph_div /= ratr_nat ratr_int lt_xr /= intrD mulrDl rmorph1.
by rewrite -(addrNK x y) -/e addrC; apply/(ltr_le_add lt_e le_rx).
Qed.

End ArchiRealFieldTheory.

(* int is archimedean *)
Module intArchimedean.
Section intArchimedean.

Fact archimedean_axiomz : Num.archimedean_axiom int_numDomainType.
Proof. by move=> x; exists (absz x).+1; rewrite natz ltz_nat ltnSn. Qed.

End intArchimedean.
End intArchimedean.

Canonical int_archiNumDomain := 
  Eval hnf in ArchiNumDomainType int intArchimedean.archimedean_axiomz.
Canonical int_archiRealDomain :=
  Eval hnf in [archiRealDomainType of int].

Section ZnatPred.

Definition Znat := (@Cnat int_archiRealDomain).
Fact Znat_key : pred_key Znat. by []. Qed.
Canonical Znat_keyed := KeyedQualifier Znat_key.

Lemma ZnatP (m : int) : reflect (exists n : nat, m = n) (m \is a Znat).
Proof. 
by apply: (iffP (CnatP m)) => [[n ->] | [n ->]]; exists n; rewrite natz.
Qed.

Lemma Znat_semiring_closed : semiring_closed Znat.
Proof. exact: (Cnat_semiring int_archiRealDomain). Qed.
Canonical Znat_addrPred := AddrPred Znat_semiring_closed.
Canonical Znat_mulrPred := MulrPred Znat_semiring_closed.
Canonical Znat_semiringPred := SemiringPred Znat_semiring_closed.

Lemma Znat_def (m : int) : (m \is a Znat) = (0 <= m).
Proof. by case: m => [m | //]; rewrite le0z_nat; apply/ZnatP; exists m. Qed.

(* relation between Znat and oldZnat. *)
Lemma Znat_old (m : int) : (m \is a Znat) = (m \is a ssrint.Znat).
Proof. by apply/ZnatP/ssrint.ZnatP. Qed.

End ZnatPred.

(* rat is archimedean *)
Canonical rat_archiNumDomain := 
  Eval hnf in ArchiNumDomainType rat rat_archimedean.
Canonical rat_archiRealDomain :=
  Eval hnf in [archiRealDomainType of rat].
Canonical rat_archiNumField :=
  Eval hnf in [archiNumFieldType of rat].
Canonical rat_archiRealField :=
  Eval hnf in [archiRealFieldType of rat].

Section QintPred.

Definition Qint := (@Cint rat_archiRealField).
Fact Qint_key : pred_key Qint. by []. Qed.
Canonical Qint_keyed := KeyedQualifier Qint_key.

Lemma QintP (x : rat) : reflect (exists z : int, x = z%:~R) (x \is a Qint).
Proof. exact: CintP. Qed.

Fact Qint_subring_closed : subring_closed Qint.
Proof. exact: (Cint_subring rat_archiRealField). Qed.
Canonical Qint_opprPred := OpprPred Qint_subring_closed.
Canonical Qint_addrPred := AddrPred Qint_subring_closed.
Canonical Qint_mulrPred := MulrPred Qint_subring_closed.
Canonical Qint_zmodPred := ZmodPred Qint_subring_closed.
Canonical Qint_semiringPred := SemiringPred Qint_subring_closed.
Canonical Qint_smulrPred := SmulrPred Qint_subring_closed.
Canonical Qint_subringPred := SubringPred Qint_subring_closed.

Lemma Qint_def (x : rat) : (x \is a Qint) = (denq x == 1).
Proof.
apply/QintP/idP => [[y ->] | /eqP H]; first by rewrite denq_int.
by exists (numq x); rewrite numqE H mulr1.
Qed.

(* relation between Qint and oldQint. *)
Lemma Qint_old (x : rat) : (x \is a Qint) = (x \is a rat.Qint).
Proof. by apply/QintP/rat.QintP. Qed.

Lemma numqK : {in Qint, cancel (fun x => numq x) intr}.
Proof. by move=> x; rewrite Qint_def numqE => /eqP ->; rewrite mulr1. Qed.

End QintPred.

Section QnatPred.

Definition Qnat := (@Cnat rat_archiRealField).
Fact Qnat_key : pred_key Qnat. by []. Qed.
Canonical Qnat_keyed := KeyedQualifier Qnat_key.

Lemma QnatP (x : rat) : reflect (exists n : nat, x = n%:R) (x \in Qnat).
Proof. exact: CnatP. Qed.

Lemma Qnat_def (x : rat) : (x \is a Qnat) = (x \is a Qint) && (0 <= x).
Proof. exact: CnatEint. Qed.

(* relation between Qnat and oldQnat. *)
Lemma Qnat_old (x : rat) : (x \is a Qnat) = (x \is a rat.Qnat).
Proof. by apply/QnatP/rat.QnatP. Qed.

Fact Qnat_semiring_closed : semiring_closed Qnat.
Proof. exact: (Cnat_semiring rat_archiRealField). Qed.
Canonical Qnat_addrPred := AddrPred Qnat_semiring_closed.
Canonical Qnat_mulrPred := MulrPred Qnat_semiring_closed.
Canonical Qnat_semiringPred := SemiringPred Qnat_semiring_closed.

End QnatPred.

(* :TODO:
Lemma Qint_dvdz (m d : int) : (d %| m)%Z -> ((m%:~R / d%:~R : rat) \is a Qint).

Lemma Qnat_dvd (m d : nat) : (d %| m)%N → ((m%:R / d%:R : rat) \is a Qnat).

+ locate other occurences
*)


(* algC is archimedean *)
Module algCArchimedean.
Section algCArchimedean.

Fact algC_archiAxiom : Num.archimedean_axiom algCnumClosedField.
Proof. 
exact: (algebraics_fundamentals.rat_algebraic_archimedean algC_algebraic). 
Qed.

End algCArchimedean.
End algCArchimedean.

Canonical algCarchiNumDomain := 
  ArchiNumDomainType algC algCArchimedean.algC_archiAxiom.
Canonical algCarchiNumFieldType := [archiNumFieldType of algC].
Canonical algCarchiNumClosedFieldType := [archiNumClosedFieldType of algC].

Section algCPred.

(* relation between Cint and oldCint. *)
Lemma Cint_old (x : algC) : (x \is a Cint) = (x \in Algebraics.Exports.Cint).
Proof. by apply/CintP/algC.CintP. Qed.

(* relation between Cnat and oldCnat. *)
Lemma Cnat_old (x : algC) : (x \is a Cnat) = (x \in Algebraics.Exports.Cnat).
Proof. by apply/CnatP/algC.CnatP. Qed.

End algCPred.


(* R[i] is archimedean if R is an archiRcfType *)
Module complexArchimedean.
Section complexArchimedean.

Variable R : archiRcfType.

Lemma complex_archimedean : 
  Num.archimedean_axiom (complex_numClosedFieldType R).
Proof.
move => z.
have R_archi : Num.archimedean_axiom R; first by case:R => ? [].
have [n] := (R_archi (ComplexField.normc z)).
move/(ler_lt_trans (ler_norm _)); rewrite -ltcR rmorphMn => lt_n.
by exists n; apply/(ltr_le_trans lt_n).
Qed.

End complexArchimedean.
End complexArchimedean.

Canonical complex_archiNumDomain (R : archiRcfType) :=
  ArchiNumDomainType R[i] (@complexArchimedean.complex_archimedean R).
Canonical complex_archiNumField (R : archiRcfType) :=
  [archiNumFieldType of R[i]].
Canonical complex_archiNumClosedField (R : archiRcfType) :=
  [archiNumClosedFieldType of R[i]].


(* realalg is archimedean *)
Module realalgArchimedean.
Section realalgArchimedean.

Fact realalg_archimedean : Num.archimedean_axiom realalg_numFieldType.
Proof. by move=> x; have := (@RealAlg.alg_archi archiType x). Qed.

End realalgArchimedean.
End realalgArchimedean.

Canonical realalg_archiNumDomainType :=
  ArchiNumDomainType realalg realalgArchimedean.realalg_archimedean.
Canonical realalg_archiNumFieldType := [archiNumFieldType of realalg].
Canonical realalg_archiRealDomainType := [archiRealDomainType of realalg].
Canonical realalg_archiRealFieldType := [archiRealFieldType of realalg].
Canonical realalg_archiRcfType := [archiRcfType of realalg].


(* complexalg is archimedean *)
Canonical complexalg_archiNumDomainType := [archiNumDomainType of complexalg].
Canonical complexalg_archiNumFieldType := [archiNumFieldType of complexalg].
Canonical complexalg_archiNumClosedFieldType := 
  [archiNumClosedFieldType of complexalg].


End Theory.

Export Archi.ArchiNumDomain.Exports Archi.ArchiNumField.Exports.
Export Archi.ArchiNumClosedField.Exports Archi.ArchiRealDomain.Exports.
Export Archi.ArchiRealField.Exports Archi.ArchiRealClosedField.Exports.

Import Theory.


Module Order.
(* complements on numClosedField *)
Section NCFComplements.

Variable R : numClosedFieldType.
Implicit Types x y : R.

(* complete order not compatible with all operations ! *)
Definition lec x y :=
    ('Re x < 'Re y) || (('Re x == 'Re y) && ('Im x <= 'Im y)).

Definition ltc x y :=
    (lec x y) && (x != y).

Notation "x <=%C y" := (lec x y) (at level 35) : ring_scope.
Notation "x <%C y" := (ltc x y) (at level 35) : ring_scope.

Lemma lecE x y :
  (x <=%C y) = ('Re x < 'Re y) || (('Re x == 'Re y) && ('Im x <= 'Im y)).
Proof. by rewrite /lec. Qed.

Lemma ltcE x y :
  (x <%C y) = (x <=%C y) && (x != y).
Proof. by rewrite /ltc. Qed.

Lemma lecc : reflexive lec.
Proof. by move=> x; rewrite lecE eq_refl lerr andbT orbT. Qed.
Hint Resolve lecc.

Lemma lec_trans : transitive lec.
Proof.
move=> x y z; rewrite !lecE => /orP[Ryx | /andP[/eqP <- Iyx]].
  move=> /orP[Rxz | /andP[/eqP <- _]].
  + by apply/orP; left; apply: (ltr_trans Ryx Rxz).
  + by rewrite Ryx.
move=> /orP[Ryz | /andP[/eqP <- Ixz]].
+ by rewrite Ryz.
+ by rewrite eq_refl (ler_trans Iyx Ixz) andbT orbT.
Qed.

Lemma lec_asym : antisymmetric lec.
Proof.
move=> x y /andP[]; rewrite !lecE => /orP[Rxy | /andP[/eqP Rxy Ixy /=]].
  move=> /orP[ | /andP[]].
  + by rewrite ltr_gtF.
  by rewrite (gtr_eqF Rxy).
move=> /orP[ | /andP[/eqP Ryx Iyx]].
+ by rewrite Rxy ltrr.
rewrite [x]Crect [y]Crect Rxy.
by move: Iyx; rewrite ler_eqVlt (ler_gtF Ixy) orbF => /eqP ->.
Qed.

Lemma ltc_neqAle x y :
  (x <%C y) = (x != y) && (x <=%C y).
Proof. by rewrite ltcE andbC. Qed.

Lemma lec_eqVlt x y :
  (x <=%C y) = (x == y) || (x <%C y).
Proof.
rewrite ltc_neqAle.
by case: (boolP (x == y)) => [/eqP -> | _ //=]; rewrite orTb lecc.
Qed.

Lemma ltcNge x y : x <%C y = ~~ (y <=%C x).
Proof.
rewrite ltcE lecE negb_or negb_and.
case: (boolP (x == y)) => [/eqP -> | ]; first by rewrite eq_refl lerr /= !andbF.
move=> x_neqy; rewrite /= andbT.
rewrite -?real_ltrNge -?real_lerNgt ?Creal_Re ?Creal_Im ?ler_eqVlt //.
have x_rect := (Crect x); have y_rect := (Crect y).
have [ | | eq_Re] //= := (real_ltrgtP (Creal_Re x) (Creal_Re y)).
have [ | | eq_Im] //= := (real_ltrgtP (Creal_Im x) (Creal_Im y)).
by move: x_neqy; rewrite x_rect y_rect eq_Re eq_Im eq_refl.
Qed.

Lemma lecNgt x y : x <=%C y = ~~ (y <%C x).
Proof. by rewrite ltcNge negbK. Qed.

Lemma ltcc x : x <%C x = false.
Proof. by rewrite ltcE eq_refl /= andbF. Qed.

Lemma ltc_trans : transitive ltc.
Proof.
move=> y x z; rewrite ltc_neqAle => /andP [_ le_xy].
rewrite !ltcNge => /negP le_zy; apply/negP => le_zx.
by apply: le_zy; apply: (lec_trans le_zx le_xy).
Qed.

Lemma neq_ltc x y :
  (x != y) = (x <%C y) || (y <%C x).
Proof.
rewrite !ltcNge -negb_and; congr (~~ _).
apply/idP/idP => [/eqP -> | H_anti]; first by rewrite andbb.
by rewrite eq_sym; apply/eqP; apply: lec_asym.
Qed.

Lemma eqc_le x y : (x == y) = (x <=%C y && y <=%C x).
Proof. by apply/eqP/idP=> [->|/lec_asym]; rewrite ?lecc. Qed.

Lemma lec_total : total lec.
Proof. by move=> x y; rewrite lec_eqVlt ltcNge -orbA orNb orbT. Qed.

Lemma ltc_le_trans y x z : x <%C y -> y <=%C z -> x <%C z.
Proof.
by move=> lt_xy; rewrite lec_eqVlt => /orP [/eqP <- // | ]; apply: ltc_trans.
Qed.

Lemma lec_lt_trans y x z : x <=%C y -> y <%C z -> x <%C z.
Proof. by rewrite lec_eqVlt => /orP [/eqP <- // | ]; apply: ltc_trans. Qed.

Lemma ltc_eqF x y : x <%C y -> (x == y) = false.
Proof. by rewrite ltcE => /andP[ _ ] /negbTE. Qed.

Lemma ltcW x y : x <%C y -> x <=%C y.
Proof. by rewrite ltcE => /andP[-> _]. Qed.

CoInductive comparec x y : bool -> bool -> bool -> bool -> bool -> bool -> Set:=
| ComparecLt : x <%C y -> comparec x y false false true false true false
| ComparecGt : y <%C x -> comparec x y false false false true false true
| ComparecEq : x = y -> comparec x y true true true true false false.

CoInductive ltc_xor_ge x y : bool -> bool -> Set :=
| LtcNotGe : x <%C y -> ltc_xor_ge x y false true
| GecNotLt : y <=%C x -> ltc_xor_ge x y true false.

CoInductive lec_xor_gt x y : bool -> bool -> Set :=
| LecNotGt : x <=%C y -> lec_xor_gt x y true false
| GtcNotLe : y <%C x -> lec_xor_gt x y false true.

Lemma ltcgtP x y :
  comparec x y (x == y) (y == x) (x <=%C y) (y <=%C x) (x <%C y) (y <%C x).
Proof.
case: (boolP (_ <%C _)) => [ltxy | nltxy].
  have H := (ltc_eqF ltxy); rewrite H; move: H; rewrite eq_sym => ->.
  rewrite ltcE; have := ltxy; rewrite ltcNge => /negbTE -> /=.
  by rewrite (ltcW ltxy); constructor.
rewrite lec_eqVlt (negbTE nltxy).
move: nltxy; rewrite -lecNgt => lexy; rewrite ltcE lexy orbF /=.
case: (boolP (_ == _)) => [/eqP eq_xy|].
  by rewrite eq_xy eq_refl /=; constructor.
rewrite eq_sym => neq_xy; rewrite (negbTE neq_xy) /=.
by constructor; rewrite ltcE lexy neq_xy.
Qed.

Lemma lecP x y : lec_xor_gt x y (x <=%C y) (y <%C x).
Proof. by case: ltcgtP => [/ltcW lexy | ltyx | ->]; constructor => //. Qed.

Lemma ltcP x y : ltc_xor_ge x y (y <=%C x) (x <%C y).
Proof. by case: ltcgtP => [/ltcW lexy | ltyx | ->]; constructor => //. Qed.


(* Monotony of addition *)
Lemma lec_add2l x : {mono +%R x : y z / y <=%C z}.
Proof.
move=> y z; rewrite lecE !raddfD /= ltr_add2l ler_add2l.
by rewrite -subr_eq0 opprD addrAC addNKr addrC subr_eq0.
Qed.

Lemma lec_add2r x : {mono +%R^~ x : y z / y <=%C z}.
Proof. by move=> y z /=; rewrite ![_ + x]addrC lec_add2l. Qed.

Lemma mono_injc f : {mono f : x y / x <=%C y} -> injective f.
Proof. by move=> mf x y /eqP; rewrite eqc_le !mf -eqc_le => /eqP. Qed.

Lemma lecW_mono f : {mono f : x y / x <=%C y} -> {mono f : x y / x <%C y}.
Proof. by move=> mf x y; rewrite !ltc_neqAle mf (inj_eq (mono_injc mf)). Qed.

Lemma lecW_mono_to (R' : eqType) (f : R -> R') (g : rel R') :
  injective f ->
  {mono f : x y / x <=%C y >-> g x y} ->
  {mono f : x y / x <%C y >-> (x != y) && g x y}.
Proof. by move=> inj_f mf x y /=; rewrite ltc_neqAle mf (inj_eq inj_f). Qed.

Lemma ltc_add2r z x y : (x + z) <%C (y + z) = x <%C y.
Proof. by rewrite (lecW_mono (lec_add2r _)). Qed.

Lemma ltc_add2l z x y : (z + x) <%C (z + y) = x <%C y.
Proof. by rewrite (lecW_mono (lec_add2l _)). Qed.

Lemma lec_add x y z t : x <=%C y -> z <=%C t -> (x + z) <=%C (y + t).
Proof.
by move=> lxy lzt; rewrite (@lec_trans (y + z)) ?lec_add2l ?lec_add2r.
Qed.

Lemma ltc_add x y z t : x <%C y -> z <%C t -> (x + z) <%C (y + t).
Proof.
by move=> lxy lzt; rewrite (@ltc_trans (y + z)) ?ltc_add2l ?ltc_add2r.
Qed.

Lemma lec_sum (I : Type) (r : seq I) (P : pred I) (F G : I -> R) :
  (forall i : I, P i -> (F i) <=%C (G i)) ->
  (\sum_(i <- r | P i) F i) <=%C (\sum_(i <- r | P i) G i).
Proof. by exact: (big_ind2 _ (lecc _) lec_add). Qed.

Lemma ltc_sum (I : Type) (r : seq I) (F G : I -> R) :
  (0 < size r)%N -> (forall i : I, (F i) <%C (G i)) ->
  (\sum_(i <- r) F i) <%C (\sum_(i <- r) G i).
Proof.
case: r => [// | x r _ Hi]; rewrite big_cons big_cons.
apply: (@ltc_le_trans (G x + \sum_(j <- r) F j)); first by rewrite ltc_add2r.
by rewrite lec_add2l; apply: lec_sum => i _; rewrite lec_eqVlt Hi orbT.
Qed.

(* lec_iff *)
Definition lecif x y (C : bool) : Prop :=
    ((x <=%C y) * ((x == y) = C))%type.

Definition lec_of_leif x y C (le_xy : lecif x y C) := le_xy.1 : x <=%C y.
Coercion lec_of_leif : lecif >-> is_true.

Lemma lecifP x y C : reflect (lecif x y C) (if C then x == y else x <%C y).
Proof.
rewrite /lecif lec_eqVlt; apply: (iffP idP)=> [|[]].
  by case: C => [/eqP->|lxy]; rewrite ?eqxx // lxy ltc_eqF.
by move=> /orP[/eqP->|lxy] <-; rewrite ?eqxx // ltc_eqF.
Qed.

Lemma lecif_refl x C : reflect (lecif x x C) C.
Proof. by apply: (iffP idP) => [-> | <-] //; split; rewrite ?eqxx. Qed.

Lemma lecif_trans x1 x2 x3 C12 C23 :
  lecif x1 x2 C12 -> lecif x2 x3 C23 -> lecif x1 x3 (C12 && C23).
Proof.
move=> ltx12 ltx23; apply/lecifP; rewrite -ltx12.
case eqx12: (x1 == x2).
  by rewrite (eqP eqx12) ltc_neqAle !ltx23 andbT; case C23.
by rewrite (@ltc_le_trans x2) ?ltx23 // ltc_neqAle eqx12 ltx12.
Qed.

Lemma lecif_le x y : x <=%C y -> lecif x y (y <=%C x).
Proof. by move=> lexy; split=> //; rewrite eqc_le lexy. Qed.

Lemma lecif_eq x y : x <=%C y -> lecif x y (x == y).
Proof. by []. Qed.

Lemma gec_lecif x y C : lecif x y C -> y <=%C x = C.
Proof. by case=> le_xy; rewrite eqc_le le_xy. Qed.

Lemma ltc_lecif x y C : lecif x y C -> (x <%C y) = ~~ C.
Proof. by move=> le_xy; rewrite ltc_neqAle !le_xy andbT. Qed.

Lemma mono_lecif (f : R -> R) C :
    {mono f : x y / x <=%C y} ->
  forall x y, (lecif (f x) (f y) C) = (lecif x y C).
Proof. by move=> mf x y; rewrite /lecif mf (inj_eq (mono_injc _)). Qed.

Lemma lecif_add x1 y1 C1 x2 y2 C2 :
    lecif x1 y1 C1 -> lecif x2 y2 C2 ->
  lecif (x1 + x2) (y1 + y2) (C1 && C2).
Proof.
rewrite -(mono_lecif _ (lec_add2r x2)) -(mono_lecif C2 (lec_add2l y1)).
exact: lecif_trans.
Qed.

Lemma lecif_sum (I : finType) (P C : pred I) (E1 E2 : I -> R) :
    (forall i, P i -> lecif (E1 i) (E2 i) (C i)) ->
  lecif (\sum_(i | P i) E1 i) (\sum_(i | P i) E2 i) [forall (i | P i), C i].
Proof.
move=> leE12; rewrite -big_andE.
elim/big_rec3: _ => [|i Ci m2 m1 /leE12]; first by rewrite /lecif lecc eqxx.
exact: lecif_add.
Qed.


(* max *)
Definition maxc x y := if (x <=%C y) then y else x.

CoInductive maxc_spec x y : bool -> bool -> R -> Set :=
| Maxc_l of x <=%C y : maxc_spec x y true false y
| Maxc_r of y <%C x : maxc_spec x y false true x.

Lemma maxcP x y : maxc_spec x y (x <=%C y) (y <%C x) (maxc x y).
Proof. by rewrite /maxc; case: lecP => H; constructor. Qed.

Lemma maxcA : associative maxc.
Proof.
move=> a b c; case: (maxcP b c); case: (maxcP a b) => //.
+ by move=> leab lebc; rewrite /maxc (lec_trans leab lebc) lebc.
+ by case: maxcP.
by move=> ltba ltcb; rewrite /maxc lecNgt (ltc_trans ltcb ltba).
Qed.

Lemma maxc_addl : left_distributive +%R maxc.
Proof. by move=> x y z; rewrite /maxc /= lec_add2r; case: ifP => _. Qed.

Lemma maxc_addr : right_distributive +%R maxc.
Proof. by move=> x y z; rewrite ![x + _]addrC maxc_addl. Qed.

Lemma maxcc x : maxc x x = x.
Proof. by rewrite /maxc lecc. Qed.

Lemma maxcC : commutative maxc.
Proof. by move=> x y; rewrite /maxc; case: (ltcgtP x y). Qed.

Lemma maxcl x y : x <=%C (maxc x y).
Proof. by case: maxcP. Qed.

Lemma maxcr x y : y <=%C (maxc x y).
Proof. by case: maxcP=> // /ltcW. Qed.


(* max of a non empty list *)
Definition bigmaxc x0 lc :=
  foldr maxc (head x0 lc) (behead lc).

Lemma bigmaxc_nil x0 : bigmaxc x0 [::] = x0.
Proof. by rewrite /bigmaxc. Qed.

Lemma bigmaxc_un x0 x :
  bigmaxc x0 [:: x] = x.
Proof. by rewrite /bigmaxc. Qed.

Lemma bigmaxc_cons x0 x y lc :
  bigmaxc x0 (x :: y :: lc) = maxc x (bigmaxc x0 (y :: lc)).
Proof.
rewrite /bigmaxc /=; elim: lc => [/= | a lc /=].
  by rewrite maxcC.
set b := foldr _ _ _; set c := foldr _ _ _ => H.
by rewrite [maxc a b]maxcC maxcA H -maxcA (maxcC c a).
Qed.

Lemma bigmaxc_lec x0 lc i :
  (i < size lc)%N -> lec (nth x0 lc i) (bigmaxc x0 lc).
Proof.
case: lc i => [i | x lc]; first by rewrite nth_nil bigmaxc_nil lecc.
elim: lc x => [x i /= | x lc /= ihlc y i i_size].
  by rewrite ltnS leqn0 => /eqP ->; rewrite nth0 bigmaxc_un /=.
rewrite bigmaxc_cons /=; case: i i_size => [_ /= | i]; first by rewrite maxcl.
rewrite ltnS /=; move/(ihlc x); move/(lec_trans)=> H; apply: H.
by rewrite maxcr.
Qed.

(* Compatibility with addition *)
Lemma bigmaxc_addr x0 lc x :
  bigmaxc (x0 + x) (map (fun y => y + x) lc) = (bigmaxc x0 lc) + x.
Proof.
case: lc => [/= | y lc]; first by rewrite bigmaxc_nil.
elim: lc y => [y | y lc ihlc z]; first by rewrite /= !bigmaxc_un.
by rewrite map_cons !bigmaxc_cons ihlc maxc_addl.
Qed.

Lemma bigmaxc_index x0 lc :
  (0 < size lc)%N -> (index (bigmaxc x0 lc) lc < size lc)%N.
Proof.
case: lc => [//= | x l _].
elim: l x => [x | x lc]; first by rewrite bigmaxc_un /= eq_refl.
move/(_ x); set z := bigmaxc _ _ => /= ihl y; rewrite bigmaxc_cons /maxc -/z.
case: (lec y z); last by rewrite eq_refl.
by case: (y == z); rewrite //.
Qed.

Lemma bigmaxc_mem x0 lc :
  (0 < size lc)%N -> bigmaxc x0 lc \in lc.
Proof. by move/(bigmaxc_index x0); rewrite index_mem. Qed.

Lemma bigmaxc_lecP x0 lc x :
  (0 < size lc)%N ->
  reflect (forall i, (i < size lc)%N -> lec (nth x0 lc i) x) (lec (bigmaxc x0 lc) x).
Proof.
move=> lc_size; apply: (iffP idP) => [le_x i i_size | H].
  by apply: (lec_trans _ le_x); apply: bigmaxc_lec.
by move/(nthP x0): (bigmaxc_mem x0 lc_size) => [i i_size <-]; apply: H.
Qed.

Lemma bigmaxcP x0 lc x :
  (x \in lc /\ forall i, (i < size lc) %N -> lec (nth x0 lc i) x) -> (bigmaxc x0 lc = x).
Proof.
move=> [] /(nthP x0) [] j j_size j_nth x_lec; apply: lec_asym; apply/andP; split.
  by apply/bigmaxc_lecP => //; apply: (leq_trans _ j_size).
by rewrite -j_nth (bigmaxc_lec _ j_size).
Qed.

Lemma bigmaxc_lecif x0 lc :
  uniq lc -> forall i, (i < size lc)%N ->
     lecif (nth x0 lc i) (bigmaxc x0 lc) (i == index (bigmaxc x0 lc) lc).
Proof.
move=> lc_uniq i i_size; rewrite /lecif (bigmaxc_lec _ i_size).
rewrite -(nth_uniq x0 i_size (bigmaxc_index _ (leq_trans _ i_size)) lc_uniq) //.
rewrite nth_index //.
by apply: bigmaxc_mem; apply: (leq_trans _ i_size).
Qed.

(* max for non-empty list (ffun I_n+1) *)
Definition bmaxf n (f : {ffun 'I_n.+1 -> R}) :=
  bigmaxc (f ord0) (codom f).

Lemma bmaxf_lec n (f : {ffun 'I_n.+1 -> R}) i :
  lec (f i) (bmaxf f).
Proof.
move: (@bigmaxc_lec (f ord0) (codom f) (nat_of_ord i)).
rewrite /bmaxf size_codom card_ord => H; move: (ltn_ord i); move/H.
suff -> : nth (f ord0) (codom f) i = f i; first by [].
by rewrite /codom (nth_map ord0) ?size_enum_ord // nth_ord_enum.
Qed.

Lemma bmaxf_index n (f : {ffun 'I_n.+1 -> R}) :
  (index (bmaxf f) (codom f) < n.+1)%N.
Proof.
rewrite /bmaxf.
have {6}-> : n.+1 = size (codom f) by rewrite size_codom card_ord.
by apply: bigmaxc_index; rewrite size_codom card_ord.
Qed.

Definition index_bmaxf n f := Ordinal (@bmaxf_index n f).

Lemma eq_index_bmaxf n (f : {ffun 'I_n.+1 -> R}) :
  f (index_bmaxf f) = bmaxf f.
Proof.
move: (bmaxf_index f).
rewrite -{3}[n.+1]card_ord -(size_codom f) index_mem.
move/(nth_index (f ord0)) => <-; rewrite (nth_map ord0).
  by rewrite -[(index _ _)]/(nat_of_ord (index_bmaxf _)) nth_ord_enum.
by rewrite size_enum_ord; apply: bmaxf_index.
Qed.

Lemma bmaxf_lecif n (f : {ffun 'I_n.+1 -> R}) :
  injective f -> forall i,
     lecif (f i) (bmaxf f) (i == index_bmaxf f).
Proof.
by move=> inj_f i; rewrite /lecif bmaxf_lec -(inj_eq inj_f) eq_index_bmaxf.
Qed.


(* ordered sequence of the roots of a polynomial *)
Definition Croots (P : {poly R}) :=
  if P == 0
  then [::]
  else sort lec (sval (closed_field_poly_normal P)).

Lemma Croots0 : Croots 0 = [::].
Proof. by rewrite /Croots eq_refl. Qed.

Lemma Croots_sorted P : sorted lec (Croots P).
Proof. by rewrite /Croots; case: ifP => // _; apply/sort_sorted/lec_total. Qed.

Lemma Croots_perm P :
  P != 0 -> perm_eq (Croots P) (sval (closed_field_poly_normal P)).
Proof. by rewrite /Croots => /negbTE ->; apply/perm_eqlP/perm_sort. Qed.

Lemma Croots_poly P : P = lead_coef P *: \prod_(x <- (Croots P)) ('X - x%:P).
Proof.
case: (boolP (P == 0)) => [/eqP -> | /negbTE P_neq0].
  by rewrite lead_coef0 scale0r.
rewrite {1}(svalP(closed_field_poly_normal P)); congr (_ *: _).
by apply/esym/eq_big_perm/Croots_perm; rewrite P_neq0.
Qed.

Lemma CrootsP P (P_neq0 : P != 0) x : reflect (root P x) (x \in Croots P).
Proof.
rewrite (perm_eq_mem (Croots_perm P_neq0)).
have lead_coef_neq0 : lead_coef P != 0; first by rewrite lead_coef_eq0.
move: P_neq0 (svalP(closed_field_poly_normal P)) => /negbTE P_neq0 {1}->.
by rewrite (rootZ _ _ lead_coef_neq0) root_prod_XsubC; apply: (iffP idP).
Qed.

Lemma Croots_neq0 P : (P != 0) -> (0 \in (Croots P)) = (P`_0 == 0).
Proof.
move=> P_neq0; apply/(CrootsP P_neq0)/eqP.
  by move/rootP; rewrite horner_coef0 => ->.
by move=> H; apply/rootP; rewrite horner_coef0.
Qed.

Lemma Croots_mu P x : (count_mem x) (Croots P) = \mu_x P.
Proof.
case: (boolP (P == 0)) =>  [/eqP P_eq0 | P_neq0].
  by rewrite P_eq0 Croots0 mu0; apply/count_memPn; rewrite in_nil.
case: (boolP (root P x)) => [x_root | x_not_root]; last first.
  by rewrite (muNroot x_not_root); apply/count_memPn/(CrootsP P_neq0)/negP.
have Hx : x \in Croots P ++ sval (closed_field_poly_normal P).
  by have /CrootsP := x_root; move=> /(_ P_neq0); rewrite mem_cat => ->.
have /allP/(_ x Hx)/eqP -> := Croots_perm P_neq0.
rewrite [in RHS](svalP (closed_field_poly_normal P)) mu_mulC ?lead_coef_eq0 //.
move: (sval _); elim => [/=|y s ihs /=]; first by rewrite big_nil mu_polyC.
rewrite big_cons mu_mul -?ihs; last first.
  by rewrite mulf_neq0 ?polyXsubC_eq0 -?size_poly_eq0 ?size_prod_XsubC.
case: (boolP (y == x)) => [/eqP -> | y_neqx /=]; first by rewrite mu_XsubC.
by rewrite muNroot // root_XsubC eq_sym y_neqx.
Qed.

Lemma Croots_size P : size (Croots P) = (size P).-1.
Proof.
case: (boolP (P == 0))=> [/eqP ->| P_neq0]; first by rewrite Croots0 size_poly0.
move: (svalP (closed_field_poly_normal P)) => H; rewrite [in RHS]H.
rewrite (perm_eq_size (Croots_perm P_neq0)) size_scale ?lead_coef_eq0 //.
by rewrite size_prod_XsubC.
Qed.

Lemma Croots_polyC c : Croots c%:P = [::].
Proof.
apply: size0nil; rewrite Croots_size size_polyC.
by case: (c == 0).
Qed.

Lemma CrootsM P Q : P * Q != 0 ->
  perm_eq (Croots (P * Q)) ((Croots P) ++ (Croots Q)).
Proof.
by move => PQ_neq0; apply/allP => x _; rewrite /= count_cat !Croots_mu mu_mul.
Qed.

Lemma CrootsZ P c : c != 0 -> Croots (c *: P) = Croots P.
Proof.
case: (boolP (P == 0)) => [/eqP -> | P_neq0 c_neq0]; first by rewrite scaler0.
apply/(eq_sorted lec_trans lec_asym); rewrite ?Croots_sorted // -mul_polyC.
apply/(perm_eq_trans (CrootsM _)); rewrite ?Croots_polyC //.
by rewrite mulf_neq0 ?polyC_eq0.
Qed.

Lemma Croots_prod (I : Type) P (r : seq I) : all [pred i | P i != 0] r ->
  perm_eq (Croots (\prod_(i <- r) P i)) (flatten [seq Croots (P i) | i <- r]).
Proof.
elim: r => [_ | j r Ihr /= /andP[Pj_neq0 Hall_neq0]]; last rewrite big_cons.
  by rewrite big_nil /= (_ : 1 = 1%:P :> {poly R}) // Croots_polyC.
apply/(perm_eq_trans (CrootsM _)); last by rewrite perm_cat2l Ihr.
by apply/mulf_neq0; rewrite ?Pj_neq0 ?prodf_seq_neq0.
Qed.

Lemma Croots_XsubC c : Croots ('X - c%:P) = [:: c].
Proof.
apply/perm_eq_small => //; apply/uniq_perm_eq => //; last first.
  move=> y; rewrite inE; have H: 'X - c%:P != 0 by rewrite polyXsubC_eq0.
  by apply/(CrootsP H)/eqP => [| -> ]; rewrite root_XsubC // => /eqP ->.
have := Croots_size ('X - c%:P); rewrite size_XsubC /=.
by case: (Croots _) => //= a l /eqP; rewrite eqSS => /eqP/size0nil ->.
Qed.

Lemma Croots_prod_XsubC rs :
  perm_eq (Croots (\prod_(x <- rs) ('X - x%:P))) rs.
Proof.
apply/(perm_eq_trans (Croots_prod _) _).
  by apply/allP => x /=; rewrite polyXsubC_eq0.
by rewrite (eq_map Croots_XsubC); elim: rs => //= x rs H /=; rewrite perm_cons.
Qed.

Lemma Croots_separable P :
  separable.separable_poly P -> uniq (Croots P).
Proof.
case: (boolP (P == 0)) => [/eqP -> _ | P_neq0]; first by rewrite Croots0.
rewrite [X in separable_poly X]Croots_poly /separable_poly.
rewrite derivZ coprimep_scalel ?coprimep_scaler ?lead_coef_eq0 //.
by rewrite -separable_prod_XsubC.
Qed.

Lemma Croots_eqp P Q :
  P %= Q -> Croots P = Croots Q.
Proof.
case: (boolP (P == 0)) => [/eqP -> | P_neq0 P_eqp_Q].
  by rewrite eqp_sym eqp0 => /eqP ->.
have Q_neq0 : Q != 0.
  by apply/(contraNneq _ P_neq0) => Q_eq0; move: P_eqp_Q; rewrite Q_eq0 eqp0.
by move/eqpf_eq : P_eqp_Q => [l /= l_neq0 ->]; apply: CrootsZ.
Qed.

End NCFComplements.

Arguments lec {R}.
Arguments ltc {R}.
Arguments maxc {R}.
Arguments Croots {R}.
Arguments lecif {R}.

End Order.



Module NormType.
(* Structures for the set of real numbers of a numDomainType *)

Section NormType.

Variable T : numDomainType.

Structure normT := NormT {nval :> T ; _ : nval \is Num.real}.

Definition normT_of of (phant T) := normT.
Identity Coercion type_normT_of : normT_of >-> normT.

End NormType.

Notation "{ 'normT' T }" := (normT_of (Phant T)).

Canonical normT_subType (T : numDomainType) := 
  Eval hnf in [subType for (@nval T)].
Definition normT_eqMixin (T : numDomainType) := 
  Eval hnf in [eqMixin of normT T by <:].
Canonical normT_eqType  (T : numDomainType) := 
  Eval hnf in EqType (normT T) (normT_eqMixin T).
Definition normT_choiceMixin  (T : numDomainType) :=
  Eval hnf in [choiceMixin of normT T by <:].
Canonical normT_choiceType (T : numDomainType) := 
  Eval hnf in ChoiceType (normT T) (normT_choiceMixin T).
Definition normT_zmodMixin (T : numDomainType) := 
  Eval hnf in [zmodMixin of normT T by <:].
Canonical normT_zmodType (T : numDomainType) := 
  Eval hnf in ZmodType (normT T) (normT_zmodMixin T).
Definition normT_ringMixin (T : numDomainType) := 
  Eval hnf in [ringMixin of normT T by <:].
Canonical normT_ringType (T : numDomainType) := 
  Eval hnf in RingType (normT T) (normT_ringMixin T).
Definition normT_comRingMixin (T : numDomainType) := 
  Eval hnf in [comRingMixin of normT T by <:].
Canonical normT_comRingType (T : numDomainType) := 
  Eval hnf in ComRingType (normT T) (@normT_comRingMixin T).
Definition normT_unitRingMixin (T : numDomainType) := 
  Eval hnf in [unitRingMixin of normT T by <:].
Canonical normT_unitRingType (T : numDomainType) := 
  Eval hnf in UnitRingType (normT T) (normT_unitRingMixin T).
Canonical normT_comUnitRingType (T : numDomainType) := 
  Eval hnf in [comUnitRingType of normT T].
Definition normT_idomainMixin (T : numDomainType) := 
  Eval hnf in [idomainMixin of normT T by <:].
Canonical normT_idomainType (T : numDomainType) := 
  Eval hnf in IdomainType (normT T) (@normT_idomainMixin T).

(*
Canonical normT_of_subType (T : numDomainType) := 
  Eval hnf in [subType of {normT T}].
Canonical normT_of_eqType (T : numDomainType) := 
  Eval hnf in [eqType of {normT T} ].
Canonical normT_of_choiceType (T : numDomainType) := 
  Eval hnf in [choiceType of {normT T}].
Canonical normT_of_zmodType (T : numDomainType) := 
  Eval hnf in [zmodType of {normT T}].
Canonical normT_of_ringType (T : numDomainType) := 
  Eval hnf in [ringType of {normT T}].
Canonical normT_of_comRingType (T : numDomainType) := 
  Eval hnf in [comRingType of {normT T}].
Canonical normT_of_unitRingType (T : numDomainType) := 
  Eval hnf in [unitRingType of {normT T}].
Canonical normT_of_comUnitRingType (T : numDomainType) := 
  Eval hnf in [comUnitRingType of {normT T}].
Canonical normT_of_idomainType (T : numDomainType) := 
  Eval hnf in [idomainType of {normT T}].*)

(* num structure *)
Section NormNumType.

Variable T : numDomainType.

Lemma nval_inj : injective (@nval T).
Proof. exact: val_inj. Qed.

Lemma nval_is_rmorphism : rmorphism (@nval T).
Proof. by []. Qed.

Program Definition normT_LeMixin := (@RealLeMixin _ 
  (fun x y => (@nval T x) <= (nval y)) (fun x y => (nval x) < (nval y)) 
  (fun x => NormT (normr_real (nval x))) _ _ _ _ _ _ _ _).
Obligation 1. by move=> x y; apply: addr_ge0. Qed.
Obligation 2. by move=> x y; apply: mulr_ge0. Qed.
Obligation 3. 
move=> [x x_re] /= H0x Hx0.
by apply/nval_inj/eqP => /=; rewrite eqr_le H0x Hx0.
Qed.
Obligation 4. by move=> x y; apply: subr_ge0. Qed.
Obligation 5. by move=> [x] /=; rewrite realE. Qed.
Obligation 6. by move=> [x x_re] /=; apply/nval_inj; rewrite /= normrN. Qed.
Obligation 7. 
by move=> [x x_re] /= H0x; apply/nval_inj; rewrite /= ger0_norm.
Qed.
Obligation 8. by move=> x y /=; rewrite ltr_def. Qed.

End NormNumType.

Canonical nval_rmorphism (T : numDomainType) := RMorphism (nval_is_rmorphism T).
Canonical nval_additive (T : numDomainType) := Additive (nval_is_rmorphism T).

Canonical normT_numDomainType (T : numDomainType) := 
  Eval hnf in NumDomainType (normT T) (normT_LeMixin T).
Canonical normT_realDomainType (T : numDomainType) :=
  Eval hnf in RealDomainType (normT T) (RealLeAxiom (normT_numDomainType T)).

(*
Canonical normT_of_numDomainType (T : numDomainType) := 
  Eval hnf in [numDomainType of {normT T}].
Canonical normT_of_realDomainType (T : numDomainType) := 
  Eval hnf in [realDomainType of {normT T}].*)

Definition normT_fieldMixin (T : numFieldType) := 
  Eval hnf in [fieldMixin of normT T by <:].
Canonical normT_fieldType (T : numFieldType) := 
  Eval hnf in FieldType (normT T) (@normT_fieldMixin T).
Canonical normT_numFieldType (T : numFieldType) := 
  Eval hnf in [numFieldType of normT T].
Canonical normT_realFieldType (T : numFieldType) := 
  Eval hnf in [realFieldType of normT T].

(*
Canonical normT_of_fieldType (T : numFieldType) := 
  Eval hnf in [fieldType of {normT T}].
Canonical normT_of_numFieldType (T : numFieldType) := 
  Eval hnf in [numFieldType of {normT T}].
Canonical normT_of_realFieldType (T : numFieldType) := 
  Eval hnf in [realFieldType of {normT T}].*)


(* {norm T} is archimedean if T is archimedean *)
(* :TODO: Remove or make it work *)
Section NormArchiType.

Variable T : archiNumDomainType.

Lemma normT_archimedean_archi : Num.archimedean_axiom (normT_numDomainType T).
Proof.
move=> x; have /archi_boundP := (normr_ge0 x); set n := bound _ => H.
by exists n; rewrite /Num.Def.ltr /= rmorph_nat; apply/(ltr_le_trans H).
Qed.

End NormArchiType.

(* {norm T} is an archimedean if T is an archi ncf *)
Section NormArchiNcfType.

Variable T : archiNumClosedFieldType.

Lemma normT_archimedean : Num.archimedean_axiom (normT_numDomainType T).
Proof.
move=> x; have /archi_boundP := (normr_ge0 x); set n := bound _ => H.
by exists n; rewrite /Num.Def.ltr /= rmorph_nat; apply/(ltr_le_trans H).
Qed.

End NormArchiNcfType.

Canonical normT_archiNumDomainType (T : archiNumClosedFieldType) :=
  Eval hnf in ArchiNumDomainType (normT T) (@normT_archimedean T).
Canonical normT_archiNumFieldType (T : archiNumClosedFieldType) := 
  Eval hnf in [archiNumFieldType of normT T].
Canonical normT_archiRealDomainType (T : archiNumClosedFieldType) := 
  Eval hnf in [archiRealDomainType of normT T].
Canonical normT_archiRealFieldType (T : archiNumClosedFieldType) := 
  Eval hnf in [archiRealFieldType of normT T].

(*
Canonical normT_of_archiNumDomainType (T : archiNumClosedFieldType) := 
  Eval hnf in [archiNumDomainType of {normT T}].
Canonical normT_of_archiNumFieldType (T : archiNumClosedFieldType) := 
  Eval hnf in [archiNumFieldType of {normT T}].
Canonical normT_of_archiRealDomainType (T : archiNumClosedFieldType) := 
  Eval hnf in [archiRealDomainType of {normT T}].
Canonical normT_of_archiRealFieldType (T : archiNumClosedFieldType) := 
  Eval hnf in [archiRealFieldType of {normT T}].
*)

Section NormRcfType.

Variable T : numClosedFieldType.

Lemma dec_factor_theorem_normT (p : {poly (normT T)}) :
  {s : seq (normT T) & {q : {poly (normT T)} | 
  p = q * \prod_(x <- s) ('X - x%:P) /\ (q != 0 -> forall x, ~~ root q x)}}.
Proof.
case: (boolP (p == 0)) => [/eqP -> | p_neq0].
  by exists [::]; exists 0; rewrite big_nil mul0r eq_refl.
pose nv := @nval T; have [r eq_p] := (closed_field_poly_normal (map_poly nv p)).
pose s : seq (normT T) := pmap insub r.
have eq_s : map nv s = filter (fun x => x \is Num.real) r.
  rewrite (pmap_filter (insubK _)).
  by apply: eq_filter => i; rewrite isSome_insub.
have Hperm : perm_eq r (map nv s ++ filter (predC (fun x => x \is Num.real)) r).
  by rewrite -(perm_filterC (fun x => x \is Num.real) r) perm_cat2r eq_s.
have Heq : map_poly nv p = nv (lead_coef p) *:
    (\prod_(x <- filter (predC (fun x => x \is Num.real)) r) ('X - x%:P)) *
    map_poly nv (\prod_(x <- s) ('X - x%:P)).
  rewrite eq_p lead_coef_map (eq_big_perm _ Hperm) big_cat /= scalerAr mulrC.
  congr (_ * _); rewrite rmorph_prod big_map /=.
  by apply/eq_bigr => i _; rewrite rmorphB /= map_polyX map_polyC.
exists s; exists (p %/ \prod_(x <- s) ('X - x%:P)); split. 
  by rewrite divpK // -(dvdp_map (@nval_rmorphism T)) /= -/nv Heq dvdp_mull. 
move=> pdivprod_neq0 x; apply/negP; rewrite rootE => /eqP/(congr1 nv)/eqP.
rewrite /nv rmorph0 -horner_map /= map_divp /= -/nv Heq mulpK; last first.
  by rewrite map_poly_eq0 monic_neq0 ?monic_prod_XsubC.
rewrite hornerZ mulf_eq0 fmorph_eq0 lead_coef_eq0 (negbTE p_neq0) /= -rootE.
by rewrite root_prod_XsubC mem_filter /=; case: x => x /= ->.
Qed.

Lemma root_conjC (x : T) (p : {poly T}) :
  root p x -> root (map_poly (fun u => u^*) p) x^*.
Proof. by rewrite !rootE horner_map => /eqP ->; rewrite conjC0. Qed.

Lemma conjM_real (x : T) : x * x^* \is Num.real.
Proof. by apply/ger0_real/mul_conjC_ge0. Qed.

Lemma conjD_real (x : T) : x + x^* \is Num.real.
Proof. by rewrite CrealE rmorphD conjCK addrC. Qed.

Definition poly_re (x : T) : {poly (normT T)} := 
  'X^2 - (NormT (conjD_real x))%:P * 'X + (NormT (conjM_real x))%:P.

Lemma poly_re_map (x : T) :
  map_poly (@nval T) (poly_re x) = ('X - x%:P) * ('X - x^*%:P).
Proof.
rewrite rmorphD rmorphB /= map_polyXn rmorphM /= map_polyX !map_polyC /=.
rewrite mulrBl !mulrBr /= opprB (_ : 'X * 'X = 'X^2) // rmorphD rmorphM /=.
by rewrite mulrDl opprD /= addrAC [in RHS]addrAC !addrA ['X * _%:P]mulrC.
Qed.

Lemma size_poly_re (x : T) :
  size (poly_re x) = 3.
Proof.
rewrite -(size_map_poly (@nval_rmorphism T)) poly_re_map.
by rewrite size_Mmonic ?polyXsubC_eq0 ?monicXsubC // !size_XsubC.
Qed.

Lemma poly_re_neq0 (x : T) : 
  (poly_re x) != 0.
Proof. by rewrite -size_poly_eq0 size_poly_re. Qed.

Lemma poly_re_root (x : T) :
  root (map_poly (@nval T) (poly_re x)) x.
Proof. by rewrite poly_re_map rootM root_XsubC eq_refl orTb. Qed.

Lemma poly_re_root_conj (x : T) :
  root (map_poly (@nval T) (poly_re x)) x^*.
Proof. by rewrite poly_re_map rootM !root_XsubC eq_refl orbT. Qed.

Lemma monic_poly_re (x : T) :
  poly_re x \is monic.
Proof.
by rewrite -(map_monic (@nval_rmorphism T)) poly_re_map rpredM ?monicXsubC.
Qed.

Lemma irredp_poly_re (x : T) :
  x \isn't Num.real -> irreducible_poly (poly_re x).
Proof.
move=> x_nre; apply: cubic_irreducible; first by rewrite size_poly_re.
move=> y; rewrite -(fmorph_root (@nval_rmorphism T)) poly_re_map rootM. 
rewrite !root_XsubC negb_or; case: eqP => [xy |_]; last case: eqP => [cy |_ //].
  by have := x_nre; rewrite -xy => {xy}; case: y => y /= ->.
have /conj_Creal : x^* \is Num.real by rewrite -cy => {cy}; case: y.
by rewrite conjCK => /esym/CrealP H; rewrite H in x_nre.
Qed.

Lemma poly_re_nroot (x : T) :
  x \isn't Num.real -> forall y, ~~ root (poly_re x) y.
Proof.
move=> x_nre y; rewrite root_factor_theorem; apply/negP => Hdiv.
have Hsize : (size ('X - y%:P) != 1%N) by rewrite size_XsubC.
have [_]:= (irredp_poly_re x_nre); move/(_ _ Hsize Hdiv)/eqp_size.
by rewrite size_XsubC size_poly_re.
Qed.

Lemma poly2_nroot (u v : normT T) :
  'X^2 - (u%:P *+ 2) * 'X + v%:P = ('X - u%:P)^+2 + (v - u^+2)%:P.
Proof.

by rewrite sqrrB mulrnAl mulrC polyC_sub polyC_exp [RHS]addrCA addrK -addrC.
Qed.

Lemma poly_re_gt0 (x : T) (y : normT T) :
  x \isn't Num.real -> (poly_re x).[y] > 0.
Proof.
move=> x_nre; rewrite /poly_re; set u := NormT _; set v := NormT _.
have Hre : (poly_re x) = ('X - (u / 2%:R) %:P)^+2 + (v - (u / 2%:R)^+2)%:P.
  rewrite /poly_re -poly2_nroot; congr (_ - _ * _ + _).
  by rewrite -polyC_muln; congr (_%:P); rewrite -mulr_natr mulfVK // pnatr_eq0.
rewrite -[X in 0 < X.[y]]/(poly_re x) Hre hornerD horner_exp -[0]addr0.
apply: (ler_lt_add (sqr_ge0 _)); rewrite !hornerE ltrNge; apply/negP.
set w := _ - _; rewrite -oppr_ge0 => H.
have sqw : sqrtC (nval (- w)) \is Num.real.
  by rewrite realE sqrtC_ge0; apply/orP; left.
have /negP := (poly_re_nroot x_nre (NormT sqw + (u /2%:R))); apply.
rewrite rootE Hre hornerD horner_exp hornerD hornerN hornerX !hornerC -/w.
by rewrite addr_eq0 addrK -(inj_eq (@nval_inj T)) rmorphX sqrtCK.
Qed.

Lemma poly_re_sg (x : T) (y : normT T) :
  x \isn't Num.real -> Num.sg (poly_re x).[y] = 1.
Proof. by move=> x_nre; apply/gtr0_sg/poly_re_gt0/x_nre. Qed.

Lemma root_factor_theorem_normT (x : T) (p : {poly (normT T)}) :
  x \isn't Num.real -> root (map_poly (@nval T) p) x = (poly_re x %| p).
Proof.
move=> x_nre; rewrite -(dvdp_map (@nval_rmorphism T)) /= poly_re_map.
rewrite Gauss_dvdp ?coprimep_XsubC ?root_XsubC -?CrealE ?x_nre //.
rewrite -!root_factor_theorem.
apply/idP/andP => [rootx | [] -> _//]; split; first by apply:rootx.
have H : conjC \o (@nval T) =1 (@nval T) by case=> i /= /CrealP.
by have := root_conjC rootx; rewrite -(map_poly_comp conjC) (eq_map_poly H).
Qed.

Lemma decomp_roots_poly (p : {poly (normT T)}) :
  {l_re : seq (normT T) & {l_im : seq T | 
    p = lead_coef p *: (\prod_(i <- l_re) ('X - i%:P) * 
                        \prod_(i <- l_im) (poly_re i)) & 
    all (fun x => x \isn't Num.real) l_im}}.
Proof.
case: (boolP (p == 0)) => [/eqP -> | p_neq0].
  by exists [::]; exists [::]; rewrite //= lead_coef0 scale0r.
have [l_re [q [eq_pq]]]:= (dec_factor_theorem_normT p).
have q_n0 : q != 0.
  by apply/(contra_neq _ p_neq0) => q_eq0; rewrite eq_pq q_eq0 mul0r.
move=> /(_ q_n0) => nrootq; exists l_re; rewrite eq_pq => {p p_neq0 eq_pq}.
have Hq : (size q).-1.+1 = size q by apply: prednK; rewrite lt0n size_poly_eq0.
move: (leqnn (size q)); rewrite -{2}Hq.
move: (size q).-1 => n; elim: n q q_n0 nrootq {Hq} => [q q_n0 _/size1_polyC H|].
  exists [::] => //; rewrite big_nil lead_coef_Mmonic ?monic_prod_XsubC //.
  by rewrite mulr1 H lead_coefC mul_polyC.
move=> n ihn q q_n0 qnroot; case: (boolP (size q == n.+2)); last first.
  by rewrite leq_eqVlt => /negbTE ->; rewrite orFb ltnS; apply: ihn.
move=> /eqP size_qeq size_qle. 
have [r eqq]:= closed_field_poly_normal (map_poly (@nval T) q).
pose x := head 0 r; have rootx : root (map_poly (@nval T) q) x.
  rewrite eqq rootZ ?lead_coef_eq0 ?map_poly_eq0 // root_prod_XsubC /x -nth0.
  apply/mem_nth; suff -> : size r = (size q).-1 by rewrite size_qeq.
  rewrite -(size_map_poly (@nval_rmorphism T)) eqq size_scale.
    by rewrite size_prod_XsubC.
  by rewrite lead_coef_eq0 map_poly_eq0 q_n0.
have x_nre : x \isn't Num.real.
  apply/negP => x_re; have /negP := qnroot (NormT x_re); apply.
  by rewrite -(fmorph_root (@nval_rmorphism T)).
have := rootx; rewrite (root_factor_theorem_normT _ x_nre) => Hdiv.
have [|y||l_im Heq Him] := (ihn (q %/ poly_re x)).
+ by rewrite (dvdp_div_eq0 Hdiv) q_n0.
+ apply/negP; rewrite root_factor_theorem => H1; have H2 := divp_dvd Hdiv.
  by have := dvdp_trans H1 H2; rewrite -root_factor_theorem; apply/negP/qnroot.
  by rewrite size_divp ?poly_re_neq0 // size_poly_re leq_subLR add2n size_qeq.
exists (x :: l_im); last by rewrite /= Him x_nre.
rewrite -(divpK Hdiv) mulrAC Heq mulrC big_cons [in RHS]mulrCA [in RHS]scalerAr.
congr (_ * (_ *: _)); set a := lead_coef _.
rewrite lead_coef_monicM ?monic_poly_re // lead_coefZ (monicP _) ?mulr1 //.
by rewrite rpredM ?rpred_prod // => i _; rewrite ?monicXsubC ?monic_poly_re.
Qed.

Lemma sgr_mono (R : realDomainType) (x y : R) : Num.sg x < Num.sg y -> x < y.
Proof.
case: sgrP => [-> | gtx0 | ltx0]; first by rewrite sgr_gt0.
  case: sgrP => _; rewrite ?ltr10 ?ltrr //.
  by rewrite -subr_lt0 opprK (_ : 1 + 1 = 2%:R) ?ltrn0.
by case: sgrP => [-> _ // | /(ltr_trans ltx0) _ // | _]; rewrite ltrr.
Qed.

Lemma normT_real_closed : Num.real_closed_axiom (normT_numFieldType T).
Proof.
move=> f a b le_ab /andP[]; rewrite ler_eqVlt => /orP[ | /ltr0_sg sg_fa].
  by rewrite -rootE => aroot _; exists a; rewrite ?lerr ?le_ab ?aroot.
rewrite ler_eqVlt => /orP[ | /gtr0_sg sg_fb].
  by rewrite eq_sym -rootE => broot; exists b; rewrite ?lerr ?le_ab ?broot.
have [l_re [l_im eq_f /allP is_im]] := decomp_roots_poly f.
have Hsg x : Num.sg f.[x] = 
             Num.sg (lead_coef f) * \prod_(i <- l_re) Num.sg ('X - i%:P).[x].
  rewrite [in LHS]eq_f hornerZ sgrM hornerM sgrM -[RHS]mulr1 mulrA.
  congr (_ * _ * _); last rewrite big_seq_cond /=.
    apply: (big_rec2 (fun i j => Num.sg i.[x] = j)).
      by rewrite hornerE sgr1.
    by move=> u p v _ Hp; rewrite hornerM sgrM Hp.
  apply: (big_rec (fun i => Num.sg i.[x] = 1)); first by rewrite hornerE sgr1.
  move=> u p; rewrite andbT=>u_in Hp; rewrite hornerM sgrM poly_re_sg ?mul1r //.
  exact: (is_im _ u_in).
have root_l_re x : x \in l_re -> root f x.
  by move=> x_in; rewrite eq_f -mul_polyC !rootM root_prod_XsubC x_in /= orbT.
have H : Num.sg (lead_coef f) != 0.
  rewrite sgr_eq0 lead_coef_eq0; apply/(contraTneq _ (introT eqP sg_fb))=> ->.
  by rewrite horner0 sgr0 eq_sym oner_neq0.
have /hasP[x x_in Hhas] : has (fun i => Num.sg ('X - i%:P).[a] 
                                     < Num.sg ('X - i%:P).[b]) l_re.
  apply/negPn/negP; rewrite -all_predC => /allP Hall; have /eqP := sg_fa.
  rewrite !Hsg big_seq_cond (eq_bigr (fun i => Num.sg ('X - i%:P).[b])).
    by rewrite -big_seq_cond -Hsg sg_fb -addr_eq0 (_ : 1 + 1 = 2%:R) ?pnatr_eq0.
  move=> x; rewrite andbT => /Hall /=; rewrite -lerNgt ler_eqVlt.
  move=> /orP[/eqP -> //|/sgr_mono]; rewrite !hornerE => Hh.
  by apply: False_rect; move: Hh; apply/negP; rewrite ltr_add2r -lerNgt le_ab.
exists x; last exact: (root_l_re x x_in).
move: Hhas; rewrite !hornerE -subr_le0 -[x <= _]subr_ge0. 
case: sgrP; case: sgrP => // _ _; rewrite ?ltrr ?ltr10 ?ltr0N1 //.
by rewrite -[-1]sub0r ltr_subr_addl (_ : 1 + 1 = 2%:R) ?ltrn0.
Qed.

End NormRcfType.

Canonical normT_rcfType (T : numClosedFieldType) := 
  Eval hnf in RcfType (normT T) (@normT_real_closed T).
Canonical normT_of_rcfType (T : numClosedFieldType) := 
  Eval hnf in [rcfType of {normT T}].

(*
Canonical normT_archiRcfType (T : archiNumClosedFieldType) := 
  [archiRcfType of normT T].
Canonical normT_of_archiRcfType (T : archiNumClosedFieldType) := 
  [archiRcfType of {normT T}].*)

End NormType.

Export NormType.

Module Algr.

Section AlgrNormT.

 Lemma poly_bound_rat {T : realFieldType} (p : {poly rat}) (a b : rat) :
  (cauchyreals.poly_bound (map_poly ratr p) (ratr a) (ratr b) =
  ratr (cauchyreals.poly_bound p a b) :> T).
Proof.
rewrite /cauchyreals.poly_bound size_map_poly rmorphD rmorph_sum rmorph1 /=.
congr (_ + _); apply/eq_bigr => i _; rewrite rmorphM rmorphX /= rmorphD /=.
by congr (_ * (_ + _) ^+ _); rewrite ratr_norm // -coef_map.
Qed.

Lemma poly_accr_bound_rat {T : realFieldType} (p : {poly rat}) (a b : rat) :
  (cauchyreals.poly_accr_bound (map_poly ratr p) (ratr a) (ratr b) =
  ratr (cauchyreals.poly_accr_bound p a b) :> T).
Proof.
rewrite /cauchyreals.poly_accr_bound size_map_poly.
rewrite rmorphM rmorphX rmorphD rmorph1 rmorph_sum /=.
congr (_ ^+ _ * (_ + _)).
  apply/eqP; rewrite eqr_le ler_maxr ler_maxl !mulr_natl -rmorphMn /=.
  rewrite (_ : (1 : T) = ratr 1) ; last by rewrite rmorph1.
  rewrite ![_ (Num.max 1 _) <= _]ler_rat !ler_maxl !lerr andbT /=.
  rewrite ![_ <= _ (Num.max 1 _)]ler_rat !ler_maxr !lerr orbT /=.
  by rewrite real_leVge // rpredMn ?num_real.
by apply/eq_bigr => i _; rewrite nderivn_map poly_bound_rat.
Qed.

(* closed intervals instead of open ones + strict :TODO: change in polyrcf *)
Lemma deriv_sign_closed {T : rcfType} (a b : T) p :
  (forall x, x \in `]a, b[ -> p^`().[x] >= 0)
  -> (forall x y, (x \in `[a, b]) && (y \in `[a, b])
    ->  x <= y -> p.[x] <= p.[y] ).
Proof.
move=> Pab x y; case/andP=> hx hy; rewrite ler_eqVlt => /orP[/eqP -> // |xy].
rewrite -subr_gte0; case: (@mvt _ x y p) => //.
move=> c hc ->; rewrite pmulr_lge0 ?subr_gt0 ?Pab //.
by apply: subitvP hc; rewrite //= ?(itvP hx) ?(itvP hy).
Qed.

(* closed intervals instead of open ones + strict :TODO: change in polyrcf *)
Lemma deriv_sign_strict {T : rcfType} (a b : T) p :
  (forall x, x \in `]a, b[ -> p^`().[x] > 0)
  -> (forall x y, (x \in `[a, b]) && (y \in `[a, b])
    ->  x < y -> p.[x] < p.[y] ).
Proof.
move=> Pab x y; case/andP=> hx hy xy.
rewrite -subr_gte0; case: (@mvt _ x y p)=> //.
move=> c hc ->; rewrite pmulr_lgt0 ?subr_gt0 ?Pab //.
by apply: subitvP hc; rewrite //= ?(itvP hx) ?(itvP hy).
Qed.

Lemma deriv0_poly0 {R : rcfType} (a b : R) p : 
  a < b -> (forall y, y \in `]a,b[ -> p.[y] == 0) -> size p = 0%N.
Proof.
rewrite -subr_gt0 => ltab Hp; apply/eqP; rewrite size_poly_eq0.
apply/negPn/negP => H; move Hn : (size p) => n; case: n Hn => [/eqP| n Hsize].
  by rewrite size_poly_eq0 (negbTE H).
pose s := mkseq (fun k => a + (k.+1)%:R * (b - a) / n.+2%:R) n.+1.
have Hall : all (root p) s.
  apply/allP => y /mapP[] i; rewrite mem_iota rootE add0n => /andP[_ lti] ->. 
  apply: Hp; rewrite inE ltr_addl divr_gt0 ?pmulr_lgt0 ?ltr0n //=.
  rewrite -ltr_subr_addl ltr_pdivr_mulr ?ltr0Sn //.
  by rewrite mulrC ltr_pmul2l // ltr_nat ltnS.
have Huniq : uniq s.
  apply/mkseq_uniq => n1 n2 /(congr1 (fun x => x - a)).
  do 2? rewrite addrAC subrr add0r.
  move/(divIf (lt0r_neq0 (ltr0Sn _ _)))/(mulIf (lt0r_neq0 ltab))/eqP.
  by rewrite eqr_nat eqSS => /eqP ->.
by have := (max_poly_roots H Hall Huniq); rewrite Hsize size_mkseq ltnS ltnn.
Qed.


(*
Section Poly_int.

(* Goal : *)
(* find the minimum of p in [a;b] *)
(* if p has no root in [a;b] then the min is > 0 *)
(* same for max *)

Variable R : rcfType.
Implicit Types p : {poly R}.
Implicit Types x y a b c : R.
Implicit Types s : seq R.

Search _ "arg".

Definition min_polyitv p a b := 
  [arg minr[a]_(i <- a :: (rcons (roots p^`() a b) b)) p.[i]].

Lemma min_polyitv0 a b : min_polyitv 0 a b = a.
Proof. 
by rewrite /min_polyitv /arg_extr filter_predT deriv0 roots0 /= !horner0 lerr.
Qed.

Lemma min_polyitv_xx p a : min_polyitv p a a = a.
Proof. by rewrite /min_polyitv /arg_extr filter_predT rootsEba /= ?lerr. Qed.

Lemma min_polyitvC x a b : min_polyitv x%:P a b = a.
Proof. 
by rewrite /min_polyitv /arg_extr filter_predT derivC roots0 /= !hornerC lerr. 
Qed.


(* We need to return a number even if the interval is empty *)
(* We return one of the bound of the interval *)
Lemma min_polyitv_gt p a b : 
  b < a -> min_polyitv p a b = if p.[a] <= p.[b] then a else b.
Proof. 
move=> /ltrW/rootsEba Hroots; rewrite /min_polyitv Hroots /=.
by rewrite /arg_extr filter_predT.
Qed.

Lemma min_polyitv_inseq p a b :
  min_polyitv p a b \in a :: (rcons (roots p^`() a b) b).
Proof.
rewrite /min_polyitv /arg_extr filter_predT /=.
elim: (rcons (roots p^`() a b) b) {2 3}a => [x|]; first by rewrite inE eq_refl.
move=> x l; set f := _ l => ihl y; case: ifP => _.
  by rewrite !inE orbCA -in_cons (ihl y) orbT.
by rewrite inE (ihl x) orbT.
Qed.

Lemma min_polyitv_in p a b :
  a <= b -> min_polyitv p a b \in `[a, b].
Proof.
move=> leab; have /allP : all (mem `[a, b]) (a :: (rcons (roots p^`() a b) b)).
  rewrite /= all_rcons /= !inE !leab !lerr /=.
  by apply/allP => x /roots_in /itvP xin /=; rewrite inE !xin.
by apply; apply: min_polyitv_inseq.
Qed.

Lemma min_polyitv_cp p a b :
  all (fun x => p.[min_polyitv p a b] <= p.[x]) 
      (a :: (rcons (roots p^`() a b) b)).
Proof.
rewrite /min_polyitv; case: arg_extrP => //=.
- by move=> x y; rewrite ler_total.
- by move=> x y z; move/ler_trans; apply.
- by rewrite inE eq_refl.
move=> x x_in ihx; rewrite ihx ?inE ?eq_refl //=.
by apply/allP => y y_in; apply: ihx; rewrite inE y_in orbT.
Qed.

Lemma min_polyitv_cpa p a b :
  p.[min_polyitv p a b] <= p.[a].
Proof. 
by have/allP/(_ a) := (min_polyitv_cp p a b); apply; rewrite inE eq_refl.
Qed.

Lemma min_polyitv_cpb p a b :
  p.[min_polyitv p a b] <= p.[b].
Proof.
have/allP/(_ b) := (min_polyitv_cp p a b); apply.
by rewrite inE mem_rcons inE eq_refl orbT.
Qed.

Lemma min_polyitv_cproots p a b x :
  x \in roots p^`() a b -> p.[min_polyitv p a b] <= p.[x].
move=> x_in; have /allP/(_ x) := (min_polyitv_cp p a b); apply.
by rewrite inE mem_rcons inE x_in !orbT.
Qed.

Lemma min_polyitv_cps p a b :
  a <= b -> all (fun x => p.[min_polyitv p a b] < p.[x])
  (filter (fun x => x < min_polyitv p a b) (a :: (rcons (roots p^`() a b) b))).
Proof.
rewrite ler_eqVlt => /orP[/eqP <-|ltab].
  by rewrite min_polyitv_xx rootsEba ?lerr //= ltrr.
apply/allP => x; rewrite mem_filter => /andP[].
have : sorted <%R (a :: (rcons (roots p^`() a b) b)).
  rewrite /= rcons_path path_roots /=.
  have := mem_last a (roots p^`() a b); rewrite inE => /orP[/eqP -> //|].
  by move/roots_in/itvP => ->.
rewrite /min_polyitv /arg_extr filter_predT.
elim: (rcons (roots p^`() a b) b) x {1 4 5 8}a.
  by move=> x a' _ ltxa; rewrite inE => /eqP h; move: ltxa; rewrite h ltrr.
move=> y l; set f := _ l => ihl x a' Hsorted.
have Hsal : sorted <%R (a' :: l).
  apply: (subseq_sorted (@ltr_trans _) _ Hsorted); rewrite /= eq_refl.
  by case: l {Hsorted ihl f} => // u s; case: ifP => _; rewrite ?subseq_cons.
have Hsyl : sorted <%R (y :: l) by have := Hsorted; rewrite /sorted => /andP[].
case: (lerP p.[a'] p.[y]) => lpay ltxf; rewrite !inE => /or3P[/eqP|/eqP|] hx.
+ by apply: ihl => //; rewrite inE hx eq_refl.
+ rewrite hx; apply: (ltr_le_trans _ lpay); apply: ihl => //.
    apply : (ltr_trans _ ltxf).
    by have := Hsorted; rewrite /sorted /path -hx => /andP[].
  by rewrite inE eq_refl.
+ by apply: ihl => //; rewrite ?inE ?hx ?orbT //.
+ rewrite hx; apply/(ler_lt_trans _ lpay). 
  rewrite /f => {f ihl lpay ltxf Hsal Hsyl Hsorted}; elim: l y => // u s.
  set f := _ s; move=> ihs v; case: ifP => [_|]; first by apply: ihs.
  by move/negP/negP; rewrite -ltrNge => /ltrW/(ler_trans (ihs _)).
+ by apply: ihl => //; rewrite ?inE ?hx ?eq_refl // -{1}hx.
by apply: ihl => //; rewrite ?inE ?hx ?orbT //=.
Qed.

Lemma min_initv p a b x :
  x \in `]a, b[ -> p^`().[x] != 0 ->
  Num.min p.[prev_root p^`() a x] p.[next_root p^`() x b] < p.[x].
Proof.
move=> x_ins p'x; set ar := prev_root p^`() a x; set br := next_root p^`() x b.
have p'n0 : p^`() != 0.
  by apply/negP => /eqP H; move: p'x; rewrite H horner0 eq_refl.
have x_inr : x \in `]ar, br[.
  by rewrite inE prev_root_lt ?next_root_gt ?(itvP x_ins) ?p'n0.
have ltabr : ar < br by rewrite (itvP x_inr).
have Hnoroot : forall y, y \in `]ar, br[ -> ~~ root p^`() y.
  move=> y; rewrite (itv_splitU2 x_inr)=>/or3P[/prev_noroot||/next_noroot] //.
  by move/eqP => ->; rewrite rootE p'x.
case: (ltrgt0P p^`().[x]) => [pgt0|plt0|/rootP]; last first.
+ by rewrite rootE (negbTE p'x).
+ apply/(@ler_lt_trans _ p.[br]); first by rewrite ler_minl lerr orbT.
  rewrite -subr_gt0 -oppr_lt0 opprD -2?hornerN subr_lt0.
  apply: (@deriv_sign_strict _ ar br); rewrite ?inE ?(itvP x_inr) ?lerr //.
  move=> y y_in; rewrite derivN hornerN oppr_gt0 -sgr_lt0.
  by rewrite (polyrN0_itv Hnoroot x_inr y_in) sgr_lt0.
apply/(@ler_lt_trans _ p.[ar]); first by rewrite ler_minl lerr.
apply: (@deriv_sign_strict _ ar br); rewrite ?inE ?(itvP x_inr) ?lerr //.
by move=> y y_in; rewrite -sgr_gt0 (polyrN0_itv Hnoroot x_inr y_in) sgr_gt0.
Qed.

Lemma min_polyitv_is_mins p a b x :
  p^`() != 0 -> x \in `[a, (min_polyitv p a b)[ -> 
  p.[min_polyitv p a b] < p.[x].
Proof.
move=> p'n0 xin.
case: (boolP (b < a)) => [ltba|]; last rewrite -lerNgt => leab.
  have: a < min_polyitv p a b by apply:(@ler_lt_trans _ x); rewrite ?(itvP xin).
  rewrite (min_polyitv_gt p ltba); case: ifP => _; rewrite ?ltrr //.
  by rewrite ltrNge ler_eqVlt ltba orbT.
case: (boolP (x == a)) => [/eqP eq_xa |].
  have /allP/(_ x):= min_polyitv_cps p leab; apply; rewrite mem_filter.
  by rewrite (itvP xin) eq_xa inE eq_refl.
rewrite neqr_lt ?(itvP xin) /= => ltax.
have x_ins : x \in `]a, b[.
  rewrite inE ltax /=; apply: (@ltr_le_trans _ (min_polyitv p a b)).
    by rewrite (itvP xin).
  by rewrite (itvP (min_polyitv_in _ _)).
case: (boolP (p^`().[x] == 0)) => [/eqP/rootP/(root_in_roots p'n0 x_ins) h|p'x].
  have /allP/(_ x):= (min_polyitv_cps p leab); apply; rewrite mem_filter.
  by rewrite (itvP xin) inE mem_rcons inE h !orbT.
have /(ler_lt_trans _):= (min_initv x_ins p'x); apply.
rewrite ler_minr; have /allP h := min_polyitv_cp p a b; rewrite !h //.
  case: next_rootP => [/eqP|y _ /rootP|y _]; first by rewrite (negbTE p'n0).
  + move=>rooty yin _; rewrite inE mem_rcons inE -root_is_roots ?rooty ?orbT //.
    by rewrite inE (ltr_trans ltax) ?(itvP yin).
  rewrite maxr_l ?(itvP x_ins) // => -> _.
  by rewrite inE mem_rcons inE eq_refl orbT.
case: prev_rootP => [/eqP|y _ /rootP|y _]; first by rewrite (negbTE p'n0).  
+ move=> rooty yin _; rewrite inE mem_rcons inE -root_is_roots ?rooty ?orbT //.
  by rewrite inE (@ltr_trans _ x y) ?(itvP yin) ?(itvP x_ins).
by rewrite minr_l ?(itvP x_ins) // => -> _; rewrite inE eq_refl.
Qed.

Lemma min_polyitv_is_min p a b x :
  x \in `[a, b] -> p.[min_polyitv p a b] <= p.[x].
Proof.
case: (boolP (p^`() == 0)) => [|p'n0].
  rewrite -size_poly_eq0 size_deriv -leqn0 -ltnS.
  by move/(leq_trans (leqSpred _))/size1_polyC => -> _; rewrite !hornerC lerr.
case: (boolP (x == a)) => [/eqP -> _|neqxa]; first by apply: min_polyitv_cpa.
case: (boolP (x == b)) => [/eqP -> _|neqxb]; first by apply: min_polyitv_cpb.
move=> x_in; have x_ins : x \in `]a, b[.
  by rewrite inE !ltr_neqAle neqxb ?(itvP x_in) eq_sym neqxa.
have leab : a <= b by apply: (@ler_trans _ x); rewrite ?(itvP x_in).
case: (boolP (p^`().[x] == 0)) => [/eqP/rootP/(root_in_roots p'n0 x_ins) h|p'x].
  have /allP/(_ x):= (min_polyitv_cp p a b); apply. 
  by rewrite inE mem_rcons inE h !orbT.
have /ltrW/(ler_trans _):= (min_initv x_ins p'x); apply.
rewrite ler_minr; have /allP h := min_polyitv_cp p a b; rewrite !h //.
  case: next_rootP => [/eqP|y _ /rootP|y _]; first by rewrite (negbTE p'n0).
  + move=>rooty yin _; rewrite inE mem_rcons inE -root_is_roots ?rooty ?orbT //.
    by rewrite inE (@ltr_trans _ x a) ?(itvP yin) ?(itvP x_ins).
  rewrite maxr_l ?(itvP x_ins) // => -> _.
  by rewrite inE mem_rcons inE eq_refl orbT.
case: prev_rootP => [/eqP|y _ /rootP|y _]; first by rewrite (negbTE p'n0).  
+ move=> rooty yin _; rewrite inE mem_rcons inE -root_is_roots ?rooty ?orbT //.
  by rewrite inE (@ltr_trans _ x y) ?(itvP yin) ?(itvP x_ins).
by rewrite minr_l ?(itvP x_ins) // => -> _; rewrite inE eq_refl.
Qed.

CoInductive min_polyitv_spec p a b : bool -> R -> Type :=
  | MinPolyitvSpecMin : 
      forall x, x \in `[a, b] -> (forall y, y \in `[a, x[ -> p.[x] < p.[y]) ->
      (forall y, y \in `[a, b] -> p.[x] <= p.[y]) ->
      min_polyitv_spec p a b (x \in `]a, b[) x
  | MinPolyitvSpecGta :
      a > b -> p.[a] <= p.[b] -> min_polyitv_spec p a b false a
  | MinPolyitvSpecGtb :
      a > b -> p.[a] > p.[b] -> min_polyitv_spec p a b false b.

Lemma min_polyitvP p a b :
  min_polyitv_spec p a b (min_polyitv p a b \in roots p^`() a b) 
                   (min_polyitv p a b).
Proof.
case: (ltrP b a) => [ltba | leab]; rewrite in_roots.
  rewrite (min_polyitv_gt p ltba) inE; case: ifP => [ltp | /negP/negP].
  + by rewrite ltrr andbF; constructor.
  by rewrite -ltrNge ltrr !andbF; constructor.
case: (boolP (p^`() == 0)) => [| p'n0].
  rewrite -size_poly_eq0 size_deriv -leqn0 -ltnS.
  move/(leq_trans (leqSpred _))/size1_polyC => -> .
  rewrite min_polyitvC !andbF.
  have <- : a \in `]a, b[ = false by rewrite inE ltrr.
  constructor; first by rewrite inE lerr leab.
  + by move=> y; rewrite inE lter_anti.
  by move=> y _; rewrite !hornerC lerr.
case: (boolP (min_polyitv p a b == a)) => [/eqP eqma|/negbTE neqma].
+ rewrite eqma inE ltrr andbF.
  have <- : a \in `]a, b[ = false by rewrite inE ltrr.
  constructor; first by rewrite inE lerr leab.
  + by move=> y; rewrite inE lter_anti.
  by move=> y y_in; rewrite -eqma; apply: min_polyitv_is_min.
case: (boolP (min_polyitv p a b == b)) => [/eqP eqmb|/negbTE neqmb].
+ rewrite eqmb inE ltrr !andbF.
  have <- : b \in `]a, b[ = false by rewrite inE ltrr andbF.
  constructor; first by rewrite inE lerr leab.
  + by move=> y; rewrite -eqmb => y_i; apply: min_polyitv_is_mins.
  by move=> y y_in; rewrite -eqmb; apply: min_polyitv_is_min.
have := min_polyitv_inseq p a b; rewrite inE mem_rcons inE neqma neqmb /=.
move/root_roots => -> /=; rewrite andbT; constructor.
+ by apply: min_polyitv_in.
+ by move=> y; apply: min_polyitv_is_mins.
by apply: min_polyitv_is_min.
Qed.

Lemma min_polyitv_eq p a b x :
  x \in `[a, b] -> (forall y, y \in `[a, x[ -> p.[x] < p.[y]) ->
  (forall y, y \in `[a, b] -> p.[x] <= p.[y]) ->
  min_polyitv p a b == x.
Proof.
move=> x_in x_mins x_min.
have ltba : (b < a) = false by apply/negP/negP; rewrite -lerNgt (itvP x_in).
case: min_polyitvP => [||]; rewrite ?ltba //.
move=> y y_in y_mins y_min; case: (ltrgtP y x) => [ltyx|ltxy|] //.
+ have /x_mins : y \in `[a, x[ by rewrite inE ltyx (itvP y_in).
  by move/(ler_lt_trans (y_min _ x_in)); rewrite ltrr.
have /y_mins : x \in `[a, y[ by rewrite inE ltxy (itvP x_in).
by move/(ler_lt_trans (x_min _ y_in)); rewrite ltrr.
Qed.

Lemma min_polyitv_split p b a c :
  b \in `[a, c] ->
  min_polyitv p a c = if (p.[min_polyitv p a b] <= p.[min_polyitv p b c])
                      then min_polyitv p a b
                      else min_polyitv p b c.
Proof.
move=> /andP[leab lebc]; case: (boolP (p^`() == 0)) => [| p'n0].
  rewrite -size_poly_eq0 size_deriv -leqn0 -ltnS.
  move/(leq_trans (leqSpred _))/size1_polyC => ->.
  by rewrite !min_polyitvC !hornerC lerr.
apply/eqP/min_polyitv_eq.
+ rewrite inE; case: ifP => _.
    by rewrite (ler_trans _ lebc) (itvP (min_polyitv_in _ leab)).
  by rewrite (ler_trans leab) (itvP (min_polyitv_in _ lebc)).  
+ case: ifP => [|/negP/negP]; rewrite -?ltrNge => ltep x /itvP x_in.
    by apply: min_polyitv_is_mins => //; rewrite inE !x_in.
  case: (ltrP x b) => ltexb.
    apply/(ltr_le_trans ltep)/min_polyitv_is_min => //.
    by rewrite inE x_in (ltrW ltexb).
  by apply/min_polyitv_is_mins => //; rewrite inE x_in ltexb.
move=> x /itvP x_in; case: ifP => [|/negP/negP]; rewrite -?ltrNge => ltep.
+ case: (ltrP x b) => ltexb.
    by apply/min_polyitv_is_min; rewrite inE x_in (ltrW ltexb).
  by apply/(ler_trans ltep)/min_polyitv_is_min; rewrite inE ltexb x_in.
case: (ltrP x b) => ltexb.
  by apply/(ler_trans (ltrW ltep))/min_polyitv_is_min; rewrite inE x_in ltrW.
by apply/min_polyitv_is_min; rewrite inE ltexb x_in.
Qed.

Lemma min_polyitv_reduce p a b c d :
  p^`() != 0 -> {subset `[c, d] <= `[a, b]} ->
  min_polyitv p a b \in `[c, d] -> min_polyitv p a b = min_polyitv p c d.
Proof.
move=> p'n0 Hsub min_in; have c_in : c \in `[a, b].
  by apply: Hsub; rewrite inE lerr (itvP min_in).
have/(min_polyitv_split p) := c_in => h.
have : min_polyitv p a b = min_polyitv p c b.
- rewrite h; move: min_in; case: ltrP => //.
  move=> ltp; rewrite h ltp => /itvP hsup.
  have /eqP ha : min_polyitv p a c == c.
    by rewrite eqr_le hsup (itvP (min_polyitv_in _ _)) ?(itvP c_in).
  apply/eqP; rewrite ha eqr_le (itvP (min_polyitv_in _ _)) ?(itvP c_in) //=.
  rewrite lerNgt; apply/negP => H.
  by move: ltp; apply/negP; rewrite ha -ltrNge min_polyitv_is_mins ?inE ?lerr.
move=> eqabc; rewrite eqabc => {h}; rewrite eqabc in min_in => {eqabc}.
have d_in : d \in `[c, b].
  have : d \in `[c, d] by rewrite inE lerr (itvP min_in).
  by move/Hsub; rewrite !inE !(itvP min_in) /= => /andP[_].
have/(min_polyitv_split p) := d_in => h.
rewrite h; move: min_in; case: lerP => //.
move=> ltp; rewrite h lerNgt ltp => /itvP hsup.
have /eqP ha : min_polyitv p d b == d.
  by rewrite eqr_le hsup (itvP (min_polyitv_in _ _)) ?(itvP d_in).
have /(min_polyitv_is_min p) : d \in `[c, d] by rewrite inE lerr (itvP d_in).
by rewrite lerNgt -{1}ha ltp.
Qed.

    
Definition max_polyitv p a b := min_polyitv (-p) a b.

Lemma max_polyitv0 a b : max_polyitv 0 a b = a.
Proof. by rewrite /max_polyitv oppr0 min_polyitv0. Qed.

Lemma max_polyitv_xx p a : max_polyitv p a a = a.
Proof. by rewrite /max_polyitv min_polyitv_xx. Qed.

Lemma max_polyitv_gt p a b : 
  b < a -> max_polyitv p a b = if p.[b] <= p.[a] then a else b.
Proof. 
by rewrite /max_polyitv => /min_polyitv_gt ->; rewrite !hornerN ler_oppl opprK.
Qed.

Lemma max_polyitv_in p a b :
  a <= b -> max_polyitv p a b \in `[a, b].
Proof. by rewrite /max_polyitv => /min_polyitv_in; apply. Qed.

Lemma max_polyitv_cpa p a b :
  p.[a] <= p.[max_polyitv p a b].
Proof. 
by rewrite /max_polyitv -[X in X <= _]opprK ler_oppl -!hornerN min_polyitv_cpa.
Qed.

Lemma max_polyitv_cpb p a b :
  p.[b] <= p.[max_polyitv p a b].
Proof.
by rewrite /max_polyitv -[X in X <= _]opprK ler_oppl -!hornerN min_polyitv_cpb.
Qed.

Lemma max_polyitv_cproots p a b x :
  x \in roots p^`() a b -> p.[x] <= p.[max_polyitv p a b].
Proof.
rewrite /max_polyitv -[X in X <= _]opprK ler_oppl -!hornerN -roots_opp -derivN.
by apply: min_polyitv_cproots.
Qed.

Lemma max_polyitv_itv p a b x :
  x \in `[a, b] -> p.[x] <= p.[max_polyitv p a b].
Proof.
rewrite /max_polyitv -[X in X <= _]opprK ler_oppl -!hornerN.
by move/min_polyitv_itv; apply.
Qed.


Definition is_min x a b p := 
  x \in `[a, b] /\ (forall y, y \in `[a,b] -> p.[x] <= p.[y]).

Lemma is_min_itv x a b p : is_min x a b p -> x \in `[a, b].
Proof. by move => []. Qed.

Lemma is_min_cp x a b p y : is_min x a b p -> y \in `[a,b] -> p.[x] <= p.[y].
Proof. by move=> [_]; apply. Qed.

Lemma is_min_gt x a b p : a > b -> ~ is_min x a b p.
Proof. by move=> gt_ab [] /itvP x_in; move: gt_ab; rewrite x_in. Qed.

Lemma is_min_xx a p : is_min a a a p.
Proof.
by split; rewrite ?inE ?lerr // => y; rewrite itv_xx => /eqP ->; rewrite lerr.
Qed.

Lemma is_min_eq x a b p : a == b -> (is_min x a b p <-> x == a).
Proof.
move=> /eqP eq_ab; rewrite /is_min; split => [/is_min_itv |/eqP ->].
  by rewrite -eq_ab itv_xx /= inE.
split; first by rewrite eq_ab inE lerr.
by move=> y; rewrite -eq_ab itv_xx /= inE => /eqP ->; rewrite lerr.
Qed.


Lemma min_deriv_sgn_const a b p :
  a < b -> (forall y, y \in `]a,b[ -> p^`().[y] == 0) -> 
  forall x, x \in `[a,b] -> is_min x a b p.
Proof.
move=> ltab Hderiv x x_in; split; first by exact: x_in.
suff : (size p <= 1)%N by move/size1_polyC => -> y _; rewrite !hornerC lerr.
have /eqP := deriv0_poly0 ltab Hderiv; rewrite size_deriv -leqn0 -ltnS.
by apply: (leq_trans (leqSpred _)).
Qed.

Lemma min_deriv_sgn_pos a b p : 
  a <= b -> (forall y, y \in `]a,b[ -> p^`().[y] >= 0) -> is_min a a b p.
Proof.
rewrite ler_eqVlt => /orP[eq_ab|]; first by have -> := is_min_eq _ _ eq_ab.
move=> ltab Hd; split; first by rewrite inE lerr (ltrW ltab).
by move=> y /itvP yin; apply: (deriv_sign_closed Hd); rewrite ?inE ?yin ?lerr.
Qed.

Lemma min_deriv_sgn_neg a b p :
  a <= b -> (forall y, y \in `]a,b[ -> p^`().[y] <= 0) -> is_min b a b p.
Proof.
rewrite ler_eqVlt => /orP[eq_ab|ltab Hd]. 
  by have -> := is_min_eq _ _ eq_ab; rewrite eq_sym.
split; first by rewrite inE lerr (ltrW ltab).
have HdN : forall y : R, y \in `]a,b[ -> (-p)^`().[y] >= 0.
  by move=> y y_in; rewrite derivN hornerN oppr_ge0 Hd.
move=> y /itvP yin; rewrite -subr_ge0 -oppr_le0 opprB -ler_subr_addl sub0r.
by rewrite -!hornerN; apply:(deriv_sign_closed HdN); rewrite ?inE ?yin ?lerr.
Qed.

Lemma min_deriv_noroot a b p :
  a <= b -> (forall y, y \in `]a,b[ -> ~~ root p^`() y) ->
  {is_min a a b p} + {is_min b a b p}.
Proof.
case: (boolP (a == b)) => [/eqP -> _ _|]; first by left; exact: is_min_xx.
move=> neqab; rewrite ler_eqVlt (negbTE neqab) /= => ltab {neqab} Hnoroot.
pose c := (a + b) / 2%:R; have c_in : c \in `]a, b[ by rewrite inE !midf_lte.
case: (ltrgt0P p^`().[c]) => [ltc | gtc | eqc]; last first.
+ by have := Hnoroot _ c_in; rewrite rootE eqc eq_refl.
+ right; apply: (min_deriv_sgn_neg (ltrW ltab)) => y y_in; apply/ltrW.
  by rewrite -sgr_lt0 (polyrN0_itv _ c_in y_in) ?sgr_lt0.
left; apply: (min_deriv_sgn_pos (ltrW ltab)) => y y_in; apply/ltrW.
by rewrite -sgr_gt0 (polyrN0_itv _ c_in y_in) ?sgr_gt0.
Qed.

Lemma min_cat a b c x y p :
  a <= b -> b <= c -> is_min x a b p -> is_min y b c p -> 
  is_min (if p.[x] <= p.[y] then x else y) a c p.
Proof.
move=> leab lebc minab minbc; split.
  case: ifP => _.
  + have /itvP x_in := is_min_itv minab; rewrite inE x_in /=.
    by apply/(ler_trans _ lebc); rewrite x_in.
  have /itvP y_in := is_min_itv minbc; rewrite inE y_in andbT.
  by apply/(ler_trans leab); rewrite y_in.
move=> z; have /(itv_splitU true) -> : b \in `[a,c] by rewrite inE leab lebc.
move=> /= /orP[z_ab|z_bc]; case: ifP.
+ by move=> _; apply: (is_min_cp minab).
+ by rewrite lerNgt => /negPn/ltrW/ler_trans; apply; apply: (is_min_cp minab).
+ by move/ler_trans; apply; apply: (is_min_cp minbc); rewrite inE !(itvP z_bc).
by move=> _; apply: (is_min_cp minbc); rewrite inE !(itvP z_bc).
Qed.

Lemma min_split a c b x p :
  a <= b -> b <= c -> is_min x a c p -> {is_min x a b p} + {is_min x b c p}.
Proof.
move=> leab lebc; have bin : b \in `[a, c] by rewrite inE leab lebc.
move=> [] /itvP x_in H; case: (lerP x b) => [lexb | ltxb].
+ left; split; first by rewrite inE lexb x_in.
  move=> y /itvP y_in; apply: H; rewrite inE y_in /=.
  by apply/(ler_trans _ lebc); rewrite y_in.
right; split; first by rewrite inE (ltrW ltxb) x_in.
move=> y /itvP y_in; apply: H; rewrite inE y_in andbT.
by apply/(ler_trans leab); rewrite y_in.
Qed.

Lemma min_split_seq a b x p s :
  a < b -> all (mem `[a,b]) s -> sorted <=%R s -> 
  (forall i, (i < (size s).+1)%N -> (forall y, 
  y \in `](nth a (a :: s) i), (nth b (a :: s) i.+1)[ -> ~~ root p^`() y)) -> 
  is_min x a b p -> x \in [:: a] ++ s ++ [::b].
Proof.
elim:s => [ltab _ _ /(_ 0%N (ltn0Sn 0%N)) /= H | lh lt].
  have [/is_min_cp Hpa | /is_min_cp Hpa] := (min_deriv_noroot (ltrW ltab) H).
  + move=> [] x_in Hpx; rewrite inE eqr_le (itvP x_in) andbT.
    case: (ltrP a x) => //= ltax; pose c := (a + b) / 2%:R.
    have c_in : c \in `]a, b[ by rewrite inE !midf_lte.
    case: (ltrgt0P p^`().[c]) => [ltc | gtc | eqc]; last first.
    + by have := H _ c_in; rewrite rootE eqc eq_refl.
    +     


have := (min_deriv_sgn_neg (ltrW ltab)). => y y_in; apply/ltrW.
  by rewrite -sgr_lt0 (polyrN0_itv _ c_in y_in) ?sgr_lt0.
left; apply: (min_deriv_sgn_pos (ltrW ltab)) => y y_in; apply/ltrW.
by rewrite -sgr_gt0 (polyrN0_itv _ c_in y_in) ?sgr_gt0.




End Poly_int.



Section Poly1.

(* Goal : construct the root of P in [a;b] in F *)

Variable R : rcfType.
Variable p : {poly rat}.
Variable a b : R.

Local Notation ratrR := (@ratr R).

Local Notation psep := (p %/ (gcdp p (deriv p))).
Local Notation x := (head 0 (roots (map_poly ratrR psep) a b)).
Local Notation pirr := (if (map_poly ratrR psep)^`().[x] > 0 then psep else -psep).

Lemma psep_root : root (map_poly ratrR psep) =1 root (map_poly ratrR p).
Proof.
move=> x /=; move: (divpK (dvdp_gcdl p (deriv p))) => eq_p.
case: (boolP (p == 0)) => [/eqP ->|pn0]; first by rewrite div0p.
apply/idP/idP => rootp; first by rewrite -eq_p rmorphM rootM /= rootp.
pose p_ := gcdp p p^`(); rewrite -mu_gt0 ?map_poly_eq0; last first.
  by apply/negP => /eqP H; move/eqP : eq_p; rewrite H eq_sym mul0r (negbTE pn0).
have fp_neq0: map_poly ratrR (psep * p_) != 0 by rewrite eq_p map_poly_eq0 pn0.
rewrite -(ltn_add2r (\mu_x (map_poly ratrR p_))) add0n -mu_mul -rmorphM //=.
rewrite divpK ?dvdp_gcdl //.
rewrite (mu_deriv_root _  rootp) ?map_poly_eq0 ?pn0 // addn1 ltnS /p_ /=.
have H := (divpK (dvdp_gcdr p p^`())).
rewrite deriv_map -{2}H rmorphM /= mu_mul ?leq_addl //.
rewrite -rmorphM H -size_poly_eq0 /= -deriv_map size_deriv -lt0n -ltnS.
have := (root_size_gt1 _ rootp); rewrite map_poly_eq0 => /(_ pn0) // => Hsize.
by rewrite prednK //= (leq_trans _ Hsize).
Qed.

Lemma psep_roots : 
  roots (map_poly ratrR psep) a b = roots (map_poly ratrR p)a b.
Proof.
case: (boolP (p == 0)) => [/eqP -> | pn0]; first by rewrite div0p.
rewrite -roots_eq ?map_poly_eq0 ?pn0 // => [y _|]; first by rewrite psep_root.
have := pn0; rewrite -{1}(divpK (dvdp_gcdl p (deriv p))).
by rewrite mulf_eq0 negb_or => /andP[].
Qed.

Lemma pirr_root :
  root (map_poly ratrR pirr) =1 root (map_poly ratrR p).
Proof. by move=> y; case: ifP => _; rewrite -psep_root ?rmorphN ?rootN. Qed.

Hypothesis p_uniq_rootR : 
  size (roots (map_poly ratrR p) a b) = 1%N.

Lemma le_ab : a <= b.
Proof.
have := (ltn0Sn 0%N); rewrite -{2}p_uniq_rootR.
by move/(mem_nth 0)/roots_in/itvP => ->.
Qed.

Lemma pn0 : p != 0.
Proof.
by apply/negP => /eqP p0; have := p_uniq_rootR; rewrite p0 map_poly0 roots0.
Qed.

Lemma psepn0 : psep != 0.
Proof.
have := pn0; rewrite -{1}(divpK (dvdp_gcdl p (deriv p))).
by rewrite mulf_eq0 negb_or => /andP[].
Qed.

Lemma psep_separable : separable_poly (map_poly ratrR psep).
Proof. by rewrite separable_map (make_separable pn0). Qed.

Lemma psep_urR : 
  size (roots (map_poly ratrR psep) a b) = 1%N.
Proof.
rewrite -p_uniq_rootR; congr (size _).
rewrite -roots_eq ?map_poly_eq0 ?psepn0 ?pn0 //.
by move=> x; rewrite psep_root.
Qed.

Lemma x_root_psep : root (map_poly ratrR psep) x.
Proof.
by rewrite -nth0; eapply root_roots; apply: mem_nth; rewrite psep_urR.
Qed.

Lemma psep_deriv_n0 : (map_poly ratrR psep)^`().[x] != 0.
Proof.
apply/negP; have := x_root_psep; rewrite -rootE -!dvdp_XsubCl => H1 H2.
have /coprimepP := psep_separable; move/(_ ('X - x%:P) H1 H2).
by rewrite polyXsubC_eqp1 /=. 
Qed.

Lemma pirr_deriv_n0 : (map_poly ratrR pirr)^`().[x] != 0.
Proof.
by case: ifP => _; rewrite ?rmorphN ?derivN ?hornerN ?oppr_eq0 /= psep_deriv_n0.
Qed.

Lemma pirr_gt0 : (map_poly ratrR pirr)^`().[x] > 0.
Proof.
case: ifP => //; rewrite rmorphN derivN hornerN lter_oppr oppr0 => /negP/negP.
by rewrite -lerNgt ler_eqVlt (negbTE psep_deriv_n0).
Qed.

 Lemma x_root_pirr : root (map_poly ratrR pirr) x.
Proof. by case: ifP => _; rewrite ?rmorphN ?rootN x_root_psep. Qed.

Lemma pirrn0 : pirr != 0.
Proof. by case: ifP => _; rewrite ?oppr_eq0 psepn0. Qed.

Lemma pirr_urR :
  size (roots (map_poly ratrR pirr) a b) = 1%N.
Proof.
rewrite -p_uniq_rootR; congr (size _); rewrite -roots_eq ?map_poly_eq0 ?pn0 //.
  by move=> x; rewrite pirr_root.
by exact: pirrn0.
Qed.

Local Notation aR := (prev_root (map_poly ratrR pirr)^`() a x).
Local Notation bR := (next_root (map_poly ratrR pirr)^`() x b).

Lemma x_inab : x \in `]a, b[. 
Proof.
by apply (@roots_in _ (map_poly ratrR psep)); rewrite -nth0 mem_nth ?psep_urR.
Qed.

Lemma x_inabR : x \in `]aR, bR[.
Proof.
have psepdn0 : (map_poly ratrR pirr)^`() != 0.
  by apply/negP => /eqP H; have := pirr_deriv_n0; rewrite H horner0 eq_refl.
by rewrite inE prev_root_lt ?next_root_gt ?(itvP x_inab) //.
Qed.

Lemma pirr_deriv y : 
  y \in `]aR, bR[ -> (map_poly ratrR pirr)^`().[y] > 0.
Proof.
rewrite (itv_splitU2 x_inabR) => /or3P[y_in|/eqP ->|y_in]. 
+ have := pirr_deriv_n0; rewrite -rootE => /sgr_neighplN /(_ _ y_in) => H.
  by rewrite -sgr_gt0 H sgr_gt0 pirr_gt0.
+ by exact: pirr_gt0.
have := pirr_deriv_n0; rewrite -rootE => /sgr_neighprN /(_ _ y_in) => H.
by rewrite -sgr_gt0 H sgr_gt0 pirr_gt0.
Qed.

Lemma pirr_0 :
  0 \in `] (map_poly ratrR pirr).[aR], (map_poly ratrR pirr).[bR] [.
Proof.
have /rootP {1}<- := x_root_pirr; rewrite inE; apply/andP; split. 
  by apply:(deriv_sign_strict pirr_deriv); rewrite ?inE ?lerr !(itvP x_inabR).
by apply: (deriv_sign_strict pirr_deriv); rewrite ?inE ?lerr !(itvP x_inabR).
Qed.

Lemma pirr_0_gene u v : u \in `[aR, x[ -> v \in `]x, bR] ->
  0 \in `] (map_poly ratrR pirr).[u], (map_poly ratrR pirr).[v] [.
Proof.
move=> u_in v_in; rewrite inE -{3 4}(rootP x_root_pirr); apply/andP; split.
apply: (deriv_sign_strict pirr_deriv); last by rewrite (itvP u_in).
+ rewrite !inE (itvP u_in) !(itvP x_inabR) /= andbT.
  by apply: (@ler_trans _ x); rewrite ?(itvP u_in) ?(itvP x_inabR).
apply: (deriv_sign_strict pirr_deriv); last by rewrite (itvP v_in).
rewrite !inE !(itvP v_in) (itvP x_inabR) /= andbT.
by apply: (@ler_trans _ x); rewrite ?(itvP x_inabR) ?(itvP v_in).
Qed.

End Poly1.

Lemma ler_mid {T : realFieldType} (a b x : T) :
  (a <= x <= b) = (`|x - (b + a) / 2%:R| <= (b - a) / 2%:R).
Proof.
rewrite ler_norml ler_subr_addl -mulrBl ler_subl_addr -mulrDl.
have -> : (b + a - (b - a)) = a * 2%:R.
  by rewrite mulr_natr mulr2n opprB addrAC addrCA subrr addr0.
have -> : (b - a + (b + a)) = b * 2%:R.
  by rewrite mulr_natr mulr2n addrAC -!addrA subrr addr0.
by rewrite !mulfK // pnatr_eq0.
Qed.

Lemma ltr_mid {T : realFieldType} (a b x : T) :
  (a < x < b) = (`|x - (b + a) / 2%:R| < (b - a) / 2%:R).
Proof.
rewrite ltr_norml ltr_subr_addl -mulrBl ltr_subl_addr -mulrDl.
have -> : (b + a - (b - a)) = a * 2%:R.
  by rewrite mulr_natr mulr2n opprB addrAC addrCA subrr addr0.
have -> : (b - a + (b + a)) = b * 2%:R.
  by rewrite mulr_natr mulr2n addrAC -!addrA subrr addr0.
by rewrite !mulfK // pnatr_eq0.
Qed.

Section Poly2.

Variable R F : rcfType.
Variable p : {poly rat}.
Variable a b e : rat.

Local Notation ratrR := (@ratr R).
Local Notation ratrF := (@ratr F).

Hypothesis lt_ab : a < b.

Hypothesis e_gt0 : e > 0.

Hypothesis p_0 :
  0 \in `] (map_poly ratrR p).[ratrR a], (map_poly ratrR p).[ratrR b] [.

Hypothesis p_derivR : 
  forall x, x \in `[(ratrR a), (ratrR b)] -> 
  (map_poly ratrR p)^`().[x] >= ratrR e.

Lemma p_derivF x :
  x \in `](ratrF a), (ratrF b)[ -> (map_poly ratrF p)^`().[x] > 0.
Proof.
move=> x_in; rewrite deriv_map.
have := (@cauchyreals.poly_accr_bound1P _ (map_poly ratr p^`())
                             (ratr ((b + a) / 2%:R)) (ratr ((b - a) / 2%:R)) x).
set m := (_ / 2%:R); set r := (_ / 2%:R).
rewrite poly_accr_bound_rat; set k := _ p^`() _ _; set k' := e / (k *+ 2) => Hk.
have lt_k'0 : k' > 0.
  apply/(divr_gt0 e_gt0); rewrite pmulrn_lgt0 //.
  by apply/cauchyreals.poly_accr_bound_gt0.
pose n := truncC ((b - a) / k').
pose n' := [arg max_(i > (@ord0 n) | x - ratr (a + k' * i%:R) >= 0) i].
have Pn'0 :  0 <= x - ratr (a + k' * (@ord0 n)%:R).
  by rewrite mulr0 addr0 subr_ge0 (itvP x_in).
have /truncC_itv/andP[] : ((b - a) / k') >= 0.
  by apply/divr_ge0/(ltrW lt_k'0); rewrite subr_ge0 (ltrW lt_ab).
rewrite -/n => le_n gt_n; pose y := (a + k' * n'%:R).
have lt_ay : a <= y.
  by rewrite -ler_subl_addl subrr mulr_natr mulrn_wge0 // (ltrW lt_k'0).
have lt_yb : y <= b.
  rewrite -ler_subr_addl mulrC -ler_pdivl_mulr ?lt_k'0 //.
  apply/(ler_trans _ le_n); rewrite ler_nat /n'; case: arg_maxP => //.
  by move=> i _ _; rewrite -ltnS; apply/ltn_ord.
have Hym : `|ratrF y - ratrF m| <= ratrF r.
  by rewrite -rmorphB -ratr_norm ler_rat /r /m -ler_mid lt_ay lt_yb.
have Hxm : `|x - ratr m| <= ratr r.
  rewrite /m /r ![ratr (_ / 2%:R)]fmorph_div rmorphD rmorphB /= ratr_nat.
  by rewrite -ler_mid !(itvP x_in).
have Hyx : `|ratr y - x| <= ratr k'.
  have Hle0 : ratr (a + k' * n'%:R) - x <= 0.
    by rewrite /n'; case: arg_maxP => // i Pi _; rewrite subr_le0 -subr_ge0.
  rewrite (ler0_norm Hle0) opprB /n'; case: arg_maxP => // im Pim Him.
  rewrite ler_subl_addl -rmorphD -addrA mulr_natr -mulrSr -mulr_natr /=.
  apply/ltrW; case: (boolP (im.+1 < n.+1)%N) => [ord_i | ].
    apply/negPn/negP; rewrite -lerNgt -subr_ge0 => H.
    by have /= := (Him (Ordinal ord_i)); move/(_ H); rewrite ltnn.
  rewrite -leqNgt ltnS leq_eqVlt leqNgt ltn_ord orbF => /eqP <-.
  apply/(@ltr_trans _ (ratr b)); first by rewrite (itvP x_in).
  by rewrite ltr_rat -ltr_subl_addl -ltr_pdivr_mull // mulrC gt_n.
have Hqd := (Hk _ Hxm Hym); have le_k0: ratrF k >= 0.
  by rewrite ler0q; apply/cauchyreals.poly_accr_bound_ge0.
have := (ler_trans Hqd (ler_pmul (normr_ge0 _) le_k0 Hyx (lerr _))).
rewrite -rmorphM /k' -mulr_natl invfM -mulrA divfK /=; last first.
   by rewrite real_neqr_lt ?num_real // cauchyreals.poly_accr_bound_gt0 orbT.
rewrite ler_norml => /andP[_]; rewrite ler_subl_addr -ler_subl_addl.
move/(ltr_le_trans _); apply; rewrite subr_gt0 horner_map ltr_rat. 
apply/(@ltr_le_trans _ e); first by rewrite ltr_pdivr_mulr // ltr_pmulr.
rewrite -(@ler_rat R) -horner_map -deriv_map /=.
by apply: p_derivR; rewrite inE ler_rat lt_ay /= ler_rat lt_yb.
Qed.

Lemma p_urF :
  size (roots (map_poly ratrF p) (ratrF a) (ratrF b)) = 1%N.
Proof.
have := (derp_root p_derivF); rewrite ler_rat => /(_ (ltrW lt_ab)).
have := p_0; rewrite !horner_map /= inE inE !ltrq0 !ltr0q => H /(_ H) {H}.
move=> [x [Hinf Hroot x_in Hsup]].
suff -> : roots (map_poly ratr p) (ratr a) (ratr b) = [:: x] by [].
apply/eqP; rewrite roots_cons rootE Hroot eq_refl x_in /=; apply/and3P; split.
+ apply/negP => /eqP/(congr1 (fun q => q.[(ratr a)]))/eqP; rewrite horner0.
  by apply/negP/ltr0_neq0/Hinf; rewrite inE lerr (itvP x_in).
+ apply/eqP/no_root_roots => y y_in; rewrite rootE.
  by apply/ltr0_neq0/Hinf; rewrite inE !(itvP y_in).
apply/eqP/no_root_roots => y y_in; rewrite rootE.
by apply/lt0r_neq0/Hsup; rewrite inE !(itvP y_in).
Qed.

End Poly2.


Section Poly3.

Variable R : archiRcfType.
Variable p : {poly rat}.
Variable a b : R.

Local Notation ratrR := (@ratr R).

Hypothesis p_urR : 
  size (roots (map_poly ratrR p) a b) = 1%N.

Local Notation psep := (p %/ (gcdp p (deriv p))).
Local Notation x := (head 0 (roots (map_poly ratrR psep) a b)).
Local Notation pirr := (if (map_poly ratrR psep)^`().[x] > 0 then psep else -psep).
Local Notation aR := (prev_root (map_poly ratrR pirr)^`() a x).
Local Notation bR := (next_root (map_poly ratrR pirr)^`() x b).

Definition e := sval (rat_dense (pirr_deriv p_urR (x_inabR p_urR))).

Lemma e_gt0 : e > 0.
Proof.
have /andP[] := svalP (rat_dense (pirr_deriv p_urR (x_inabR p_urR))).
by rewrite ltr0q.
Qed.

Lemma e_lt : ratrR e < (map_poly ratrR pirr)^`().[x].
Proof.
by have /andP[_] := svalP (rat_dense (pirr_deriv p_urR (x_inabR p_urR))).
Qed.

Local Notation pe := ((map_poly ratrR pirr)^`() - (ratrR e)%:P).

Lemma pe_x : pe.[x] != 0.
Proof. by rewrite gtr_eqF // !hornerE subr_gt0 e_lt. Qed.

Lemma pre_u : prev_root pe aR x < x.
Proof.
apply/prev_root_lt/negP; first by rewrite (itvP (x_inabR p_urR)).
by move/eqP/(congr1 (fun q => q.[x]))/eqP; rewrite horner0 (negbTE pe_x).
Qed.

Definition u := sval (rat_dense pre_u).

Lemma u_in : ratrR u \in `[aR, x[.
Proof.
have /andP[] := svalP (rat_dense pre_u); rewrite -/u inE => Hru ->.
rewrite andbT; apply/ltrW/(ler_lt_trans _ Hru).
have /andP[H _] := prev_root_in pe aR x.
by move/(ler_trans _): H; apply; rewrite ler_minr lerr (itvP (x_inabR p_urR)).
Qed.

Lemma u_gt : ratrR u > prev_root pe aR x.
Proof. by have /andP[->] := svalP (rat_dense pre_u). Qed.

Lemma pre_v : next_root pe x bR > x.
Proof.
apply/next_root_gt/negP; first by rewrite (itvP (x_inabR p_urR)).
by move/eqP/(congr1 (fun q => q.[x]))/eqP; rewrite horner0 (negbTE pe_x).
Qed.

Definition v := sval (rat_dense pre_v).

Lemma v_in : ratrR v \in `]x, bR].
Proof.
have /andP[] := svalP (rat_dense pre_v); rewrite -/v inE => -> Hrv /=. 
apply/ltrW/(ltr_le_trans Hrv).
have /andP[_] := next_root_in pe x bR.
by move/ler_trans; apply; rewrite ler_maxl lerr (itvP (x_inabR p_urR)).
Qed.

Lemma v_lt : ratrR v < next_root pe x bR.
Proof. by have /andP[_ ->] := svalP (rat_dense pre_v). Qed.

Lemma lt_uv : u < v.
Proof.
rewrite -(ltr_rat R).
by apply: (@ltr_trans _ x); rewrite ?(itvP u_in) ?(itvP v_in).
Qed.

Lemma p_0 :
  0 \in `] (map_poly ratrR pirr).[ratrR u], (map_poly ratrR pirr).[ratrR v] [.
Proof. by exact: (pirr_0_gene p_urR u_in v_in). Qed.

Lemma p_0_gene y z : y \in `[(ratrR u), x[ -> z \in `]x, (ratrR v)] ->
  0 \in `] (map_poly ratrR pirr).[y], (map_poly ratrR pirr).[z] [.
Proof.
move=> y_in z_in; apply: (pirr_0_gene p_urR); rewrite inE.
+ rewrite (itvP y_in) andbT.
  by apply: (@ler_trans _ (ratr u)); rewrite ?(itvP y_in) ?(itvP u_in).
rewrite (itvP z_in) /=.
by apply: (@ler_trans _ (ratr v)); rewrite ?(itvP z_in) ?(itvP v_in).
Qed.

Lemma p_derivR : 
  forall y, y \in `[(ratrR u), (ratrR v)] -> 
  (map_poly ratrR pirr)^`().[y] >= ratrR e.
Proof.
move=> y; rewrite -subr_ge0 -(hornerC (ratr e) y) -hornerN -hornerD -sgr_ge0.
rewrite (@itv_splitU2 _ x); last by rewrite inE (itvP u_in) (itvP v_in).
have pe_lt : Num.sg pe.[x] > 0 by rewrite sgr_gt0 !hornerE subr_gt0 e_lt.
move/or3P => [y_inux|/eqP ->|y_inxv]; apply/ltrW => //; last first.
+ have y_in : y \in neighpr pe x bR.
    rewrite /neighpr inE (itvP y_inxv) /=.
    by apply: (ler_lt_trans _ v_lt); rewrite (itvP y_inxv).
  by rewrite (sgr_neighprN pe_x y_in). 
have y_in : y \in neighpl pe aR x.
  rewrite /neighpl inE (itvP y_inux) andbT.
  by apply: (ltr_le_trans u_gt); rewrite (itvP y_inux).
by have := pe_x; rewrite -rootE => /sgr_neighplN /(_ _ y_in) ->.
Qed.

Lemma x_in : x \in `](ratrR u), (ratrR v)[.
Proof. by rewrite inE (itvP u_in) (itvP v_in). Qed.

End Poly3.

Lemma roots_cat (R : rcfType) (x a b : R) (p : {poly R}) :
  x \in `[a, b] -> ~~ root p x -> roots p a b = roots p a x ++ roots p x b.
Proof.
case: (boolP (p == 0)) => [/eqP -> |pn0]; first by rewrite !roots0.
rewrite inE !ler_eqVlt => /andP[] /orP[/eqP -> _|lt_ax /orP[/eqP ->|lt_xb nrx]].
    by rewrite (rootsEba p (lerr x)) /=.
  by rewrite (rootsEba p (lerr b)) cats0.
apply/esym/(roots_uniq pn0).
  apply/(cat_roots_on _ nrx)/roots_on_roots/pn0/roots_on_roots/pn0.
  + by rewrite inE lt_ax lt_xb.
  + by apply/sorted_roots.
  by apply/sorted_roots.
eapply (@path_sorted _ _ a); rewrite cat_path path_roots /=.
have /allP H := order_path_min (@ltr_trans _) (@path_roots R p x b).
rewrite path_min_sorted ?sorted_roots // => y /H /(ltr_trans _); apply.
by apply: last_roots_le. 
Qed.

Section Poly4.

Variable R : archiRcfType.
Variable p : {poly rat}.
Variable a b : rat.
Variable F : rcfType.

Local Notation ratrR := (@ratr R).
Local Notation ratrF := (@ratr F).
 
Hypothesis p_urR : 
  size (roots (map_poly ratrR p) (ratrR a) (ratrR b)) = 1%N.

Lemma p_uniq_rootF : 
  size (roots (map_poly ratrF p) (ratrF a) (ratrF b)) = 1%N.
Proof.
pose psep := (p %/ (gcdp p (deriv p))).
pose x := (head 0 (roots (map_poly ratrR psep) (ratrR a) (ratrR b))).
pose pirr := (if (map_poly ratrR psep)^`().[x] > 0 then psep else -psep).
pose aR := (prev_root (map_poly ratrR pirr)^`() (ratrR a) x).
pose bR := (next_root (map_poly ratrR pirr)^`() x (ratrR b)).
pose up := u p_urR.
pose vp := v p_urR.
pose ep := e p_urR.
have : size (roots (map_poly ratrF pirr) (ratr up) (ratr vp)) = 1%N.
  by apply/p_urF/p_derivR/p_0/e_gt0/lt_uv.
have pn0 : map_poly ratrF p != 0 by rewrite map_poly_eq0; apply: (pn0 p_urR).
have psepn0 : map_poly ratrF psep != 0 by rewrite map_poly_eq0 (psepn0 p_urR).
have pirrn0 : map_poly ratrF pirr != 0 by rewrite map_poly_eq0 (pirrn0 p_urR).
have: {in `](ratr a), (ratr b)[, 
  root (map_poly ratrF p) =1 root (map_poly ratrF pirr)}.
  by move=> y _; rewrite /pirr; case: ifP=>_; rewrite ?rmorphN ?rootN psep_root.
rewrite roots_eq // => ->.
have := (p_0 p_urR); rewrite inE !horner_map /= ltr0q ltrq0 => /andP[ltu ltv].
have int_sub : {subset `[(ratrF up), (ratrF vp)] <= `[(ratrF a), (ratrF b)]}.
  apply: subitvP => /=; rewrite !ler_rat -!(ler_rat R); apply/andP; split.
    apply/(@ler_trans _ aR); rewrite ?(itvP (u_in p_urR)) //.
    have := (prev_root_in (map_poly ratrR pirr)^`() (ratr a) x).
    rewrite inE => /andP[/(ler_trans _) H _]; apply: H; rewrite ler_minr lerr.
    by rewrite (itvP (x_inab p_urR)).
  apply/(@ler_trans _ bR); rewrite ?(itvP (v_in p_urR)) //.
  have := (next_root_in (map_poly ratrR pirr)^`() x (ratr b)).
  rewrite inE => /andP[_ /ler_trans]. 
  by apply; rewrite ler_maxl lerr (itvP (x_inab p_urR)).
rewrite (@roots_cat _ (ratr up) (ratr a)); last first.
+ by rewrite rootE; apply/ltr0_neq0; rewrite horner_map ltrq0 ltu. 
+ by apply/int_sub; rewrite inE lerr ler_rat (ltrW (lt_uv _)).
rewrite (@roots_cat _ (ratr vp) _ (ratr b)); last first.
+ by rewrite rootE; apply/lt0r_neq0; rewrite horner_map ltr0q ltv. 
+ suff : ratrF vp \in `[(ratr up), (ratr vp)].
    by move/int_sub => /itvP H; rewrite inE H ler_rat (ltrW (lt_uv _)).
  by rewrite inE lerr ler_rat (ltrW (lt_uv _)).
rewrite !size_cat => ->; apply/eqP; rewrite add1n addnS eqSS addn_eq0.
set f := ratr.
Search _ (_ + _ == 0)%N in ssrnat.








Lemma p_urF :
  size (roots (map_poly ratrF p) (ratrF a) (ratrF b)) = 1%N.




(* (* :TODO: move and find a better proof : too long *) *)
(* (* should probably be on an idomain *) *)
(* Lemma mu_gcdp {T : fieldType} (p q : {poly T}) (x : T) : *)
(*   p * q != 0 -> \mu_x (gcdp p q) = minn (\mu_x p) (\mu_x q). *)
(* Proof. *)
(* move=> pq_n0; have := pq_n0; rewrite mulf_eq0 negb_or => /andP[p_n0 q_n0]. *)
(* have g_n0 : gcdp p q != 0 by rewrite gcdp_eq0 (negbTE p_n0) (negbTE q_n0). *)
(* rewrite -[in minn _ _](divpK (dvdp_gcdr p q)) -[in minn _](divpK (dvdp_gcdl p q)). *)
(* rewrite !mu_mul ?divpK ?dvdp_gcdr ?dvdp_gcdl // -addn_minl -[LHS]add0n. *)
(* apply/eqP; rewrite eqn_add2r eq_sym -leqn0 geq_min. *)
(* case: (boolP (root (p %/ gcdp p q) x)) => [root_pg | /muNroot -> //]. *)
(* have/coprimep_div_gcd/coprimep_root : (p != 0) || (q != 0) by rewrite p_n0. *)
(* by move/(_ _ root_pg); rewrite -rootE => /muNroot ->; rewrite leqnn orbT. *)
(* Qed. *)

(* (* :TODO: remove once the changes are made in polyorder *) *)
(* Lemma size_deriv (R : numDomainType) (p : {poly R}) : size p^`() = (size p).-1. *)
(* Proof. *)
(* have [lep1|lt1p] := leqP (size p) 1. *)
(*   by rewrite {1}[p]size1_polyC // derivC size_poly0 -subn1 (eqnP lep1). *)
(* rewrite size_poly_eq // mulrn_eq0 -subn2 -subSn // subn2. *)
(* by rewrite lead_coef_eq0 -size_poly_eq0 -(subnKC lt1p). *)
(* Qed. *)

(* (* :TODO: remove once the changes are made in polyorder *) *)
(* Lemma mu_deriv (R : numDomainType) : forall x (p : {poly R}), root p x -> *)
(*   \mu_x (p^`()) = (\mu_x p - 1)%N. *)
(* Proof. *)
(* move=> x p px0; have [-> | nz_p] := eqVneq p 0; first by rewrite derivC mu0. *)
(* have [q nz_qx Dp] := mu_spec x nz_p. *)
(* case Dm: (\mu_x p) => [|m]; first by rewrite Dp Dm mulr1 (negPf nz_qx) in px0. *)
(* rewrite subn1 Dp Dm !derivCE exprS mul1r mulrnAr -mulrnAl mulrA -mulrDl. *)
(* rewrite cofactor_XsubC_mu // rootE !(hornerE, hornerMn) subrr mulr0 add0r. *)
(* by rewrite mulrn_eq0. *)
(* Qed. *)

(* (* :TODO: remove once the changes are made in polyorder *) *)
(* Lemma mu_deriv_root (R : numDomainType) :  *)
(*   forall x (p : {poly R}), p != 0 -> root p x -> *)
(*   \mu_x p  = (\mu_x (p^`()) + 1)%N. *)
(* Proof. *)
(* by move=> x p p0 rpx; rewrite mu_deriv // subn1 addn1 prednK // mu_gt0. *)
(* Qed. *)

(* (* :TODO: add in separable *) *)
(* Lemma separable_polyZ (R : idomainType) (p : {poly R}) (a : R) :  *)
(*     a != 0 -> separable_poly (a *: p) = separable_poly p. *)
(* Proof. *)
(* by move=> an0; rewrite /separable_poly derivZ coprimep_scalel ?coprimep_scaler. *)
(* Qed. *)

(* Notation psep p := (p %/ (gcdp p (deriv p))). *)

(* Lemma psep_XsubC (R : idomainType) (x : R) : *)
(*   psep ('X - x%:P) = 'X - x%:P. *)
(* Proof. *)
(* rewrite derivXsubC /gcdp /gcdp_rec size_XsubC size_poly1 /= polyXsubC_eq0. *)
(* by rewrite size_XsubC /= modp1 eq_refl /= divp1. *)
(* Qed. *)

(* Lemma psep_separable (R : idomainType) (p : {poly R}) : *)
(*   p != 0 -> separable_poly (psep p). *)
(* Proof. by move=> p_neq0; rewrite make_separable. Qed. *)

(* Lemma psep_eq0 (R : idomainType) (p : {poly R}) : *)
(*   (psep p == 0) = (p == 0). *)
(* Proof. by rewrite dvdp_div_eq0 ?dvdp_gcdl. Qed. *)

(* Lemma psep_neq0 (R : idomainType) (p : {poly R}) : *)
(*   p != 0 -> psep p != 0. *)
(* Proof. by rewrite psep_eq0. Qed. *)

(* Lemma gcdpN (R : fieldType) (p q : {poly R}) : *)
(*   gcdp (-p) (-q) = - gcdp p q. *)
(* Proof. *)
(* case: (boolP (p == 0)) => [/eqP -> |pn0]; first by rewrite oppr0 !gcd0p. *)
(* case: (boolP (q == 0)) => [/eqP -> |qn0]; first by rewrite oppr0 !gcdp0. *)
(* rewrite /gcdp /gcdp_rec !size_opp /=. *)
(* have Hmod (u : {poly R}) v : v != 0 -> -u %% -v = - u %% v. *)
(*   move=> vn0; have := (divp_eq (- u) (v)); rewrite -mulrNN. *)
(*   by move/modpP => -> //; rewrite size_opp; apply: ltn_modpN0. *)
(* case: ifP; rewrite oppr_eq0; case: ifP => // _ _; rewrite size_opp. *)
(*   move: (size q) => n; elim: n p q pn0 qn0 => [p q pn0 qn0|]. *)
(*     by rewrite (Hmod _ _ pn0) modp_opp oppr_eq0; case: ifP. *)
(*   move=> n ihn p q pn0 qn0; rewrite (Hmod _ _ pn0) modp_opp oppr_eq0. *)
(*   by case: ifP => // /negbT qpn0; apply: ihn => //. *)
(* move: (size p) => n; elim: n p q pn0 qn0 => [p q pn0 qn0|]. *)
(*   by rewrite (Hmod _ _ qn0) modp_opp oppr_eq0; case: ifP. *)
(* move=> n ihn p q pn0 qn0; rewrite (Hmod _ _ qn0) modp_opp oppr_eq0. *)
(* by case: ifP => // /negbT pqn0; apply: ihn => //. *)
(* Qed. *)

(* Lemma psepN (R : numFieldType) (p : {poly R}) : *)
(*   psep (-p) = (psep p). *)
(* Proof. *)
(* case: (boolP (p == 0)) => [/eqP -> | pn0]; first by rewrite oppr0. *)
(* rewrite divp_opp derivN gcdpN; move H : (gcdp _ _) => q. *)
(* have := (divp_eq p (-q)); rewrite mulrN -mulNr => /divpP -> //.  *)
(* rewrite -[X in (_ < X)%N]size_opp; apply: ltn_modpN0. *)
(* by rewrite -H oppr_eq0 gcdp_eq0 (negbTE pn0). *)
(* Qed. *)

(* Lemma psep_root (F : numFieldType) (p : {poly F}) : *)
(*   root (psep p) =1 root p. *)
(* Proof. *)
(* case: (boolP (p == 0)) => [/eqP -> | p_n0]; first by rewrite div0p. *)
(* move=> x /=; move: (divpK (dvdp_gcdl p (deriv p))) => eq_p. *)
(* apply/idP/idP => rootp; first by rewrite -eq_p rootM /= rootp. *)
(* pose p_ := gcdp p p^`(); rewrite -mu_gt0; last first. *)
(*   apply/negP => /eqP H; rewrite H mul0r in eq_p. *)
(*   by rewrite -eq_p eq_refl in p_n0. *)
(* have fp_neq0 : (p %/ p_) * p_ != 0 by rewrite eq_p. *)
(* rewrite -(ltn_add2r (\mu_x p_)) add0n -mu_mul //. *)
(* rewrite divpK ?dvdp_gcdl //. *)
(* rewrite (mu_deriv_root _  rootp) // addn1 ltnS /p_ /=.  *)
(* have H := (divpK (dvdp_gcdr p p^`())). *)
(* rewrite -{2}H mu_mul ?leq_addl // H -size_poly_eq0 size_deriv. *)
(* rewrite -lt0n -ltnS prednK; last by rewrite lt0n size_poly_eq0. *)
(* by apply: (root_size_gt1 _ rootp). *)
(* Qed. *)

(* Lemma psep_map (F : fieldType) (rR : idomainType) (f : {rmorphism F -> rR}) p : *)
(*   map_poly f (psep p) = psep (map_poly f p). *)
(* Proof. by rewrite deriv_map -gcdp_map map_divp. Qed. *)

(* Lemma psep_roots (F : rcfType) (p : {poly F}) a b : *)
(*   roots (psep p) a b = roots p a b. *)
(* Proof. *)
(* case: (boolP (p == 0)) => [/eqP -> | pn0]; first by rewrite div0p. *)
(* have psn0 := psep_neq0 pn0; rewrite -(roots_eq _ _ psn0 pn0) => x _. *)
(* by rewrite psep_root. *)
(* Qed. *)

(* Lemma psep_mu_root (R : numFieldType) (p : {poly R}) (x : R) : *)
(*    p != 0 -> root p x -> \mu_x (psep p) = 1%N. *)
(* Proof. *)
(* move=> pn0 rootpx; apply/esym/eqP; rewrite -(muP _ _ (psep_neq0 pn0)) expr1. *)
(* rewrite dvdp_XsubCl psep_root rootpx /=. *)
(* have := (separable_coprime (psep_separable pn0)); rewrite poly_square_freeP. *)
(* by apply; rewrite size_XsubC. *)
(* Qed. *)

(* Definition sgpr {aR : realDomainType} (p : {poly aR}) x := *)
(*   let fix aux (p : {poly aR}) n := *)
(*   if n is n'.+1 *)
(*     then if ~~ root p x *)
(*       then Num.sg p.[x] *)
(*       else aux p^`() n' *)
(*     else 0 *)
(*       in aux p (size p). *)

(* Lemma sgpr_map (fR : realFieldType) (aR : realDomainType)  *)
(*   (f : {rmorphism fR -> aR}) (f_mono : {mono f : x y / x <= y >-> x <= y}) p x : *)
(*   sgpr (map_poly f p) (f x) = f (sgpr p x). *)
(* Proof. *)
(* rewrite /sgpr size_map_poly. *)
(* elim: (size p) {1 3}p => {p} [|n ihn p]; first by rewrite rmorph0. *)
(* case: ifP; rewrite fmorph_root ?horner_map => ->; last by rewrite deriv_map ihn. *)
(* apply/esym; case: sgrP => [-> ||]; first by rewrite !rmorph0 sgr0.  *)
(*   by rewrite rmorph1 -(lerW_mono f_mono) rmorph0 => /gtr0_sg ->. *)
(* by rewrite rmorphN1 -(lerW_mono f_mono) rmorph0 => /ltr0_sg ->. *)
(* Qed. *)

(* Lemma sgpr_sgp_right {R : rcfType} (p : {poly R}) x : *)
(*   sgpr p x = sgp_right p x. *)
(* Proof. by []. Qed. *)

(* Lemma sgpr_deriv (R : realDomainType) (p : {poly R}) (x : R) : *)
(*   root p x -> sgpr p x = sgpr p^`() x. *)
(* Proof. *)
(* case: (size p) {-2}p (erefl (size p)) x => {p} [p|n p sp x]. *)
(*   by move/eqP; rewrite size_poly_eq0; move/eqP => -> x _; rewrite deriv0. *)
(* by rewrite /sgpr size_deriv sp /= => ->. *)
(* Qed. *)

(* Lemma sgprNroot (R : realDomainType) (p : {poly R}) (x : R) : *)
(*   ~~ root p x -> sgpr p x = Num.sg p.[x]. *)
(* Proof. *)
(* case: (boolP (p == 0)) => [/eqP -> | pn0 rootNpx]; first by rewrite root0. *)
(* rewrite /sgpr; suff -> : size p = (size p^`()).+1 by rewrite rootNpx. *)
(* by rewrite size_deriv prednK // size_poly_gt0. *)
(* Qed. *)

(* (* :TODO: modif in sgp_right_eq0 *) *)
(* Lemma sgpr_eq0 (R : realDomainType) p (x : R) : (sgpr p x == 0) = (p == 0). *)
(* Proof. *)
(* case: (altP (p =P 0))=> [->|p0]; first by rewrite /sgpr size_poly0 eq_refl. *)
(* rewrite /sgpr. *)
(* elim: (size p) {-2}p (erefl (size p)) p0=> {p} [|sp ihsp] p esp p0. *)
(*   by move/eqP:esp; rewrite size_poly_eq0 (negPf p0). *)
(* rewrite esp /=; case px0: root=> //=; rewrite ?sgr_cp0 ?px0//. *)
(* have hsp: sp = size p^`() by rewrite size_deriv esp. *)
(* rewrite hsp ihsp // -size_poly_eq0 -hsp; apply/negP; move/eqP=> sp0. *)
(* by have := root_size_gt1 p0 px0; rewrite esp sp0 ltnn. *)
(* Qed. *)

(* CoInductive sgpr_spec {R : realDomainType} (p : {poly R}) (x : R) : *)
(*   R -> R -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Type := *)
(* | Sgpr0 : p = 0 -> *)
(*            sgpr_spec p x 0 0 true false true false false false false true true true *)
(* | SgprPosR : p != 0 -> root p x -> sgpr p^`() x = 1 -> *)
(*            sgpr_spec p x 1 0 false true false true false true false true false true *)
(* | SgprPosNr : p != 0 -> p.[x] > 0 -> *)
(*            sgpr_spec p x 1 1 false true false true false true false true false false *)
(* | SgprNegR : p != 0 -> root p x -> sgpr p^`() x = -1 -> *)
(*            sgpr_spec p x (-1) 0 false true false false true false true false true true *)
(* | SgprNegNr : p != 0 -> p.[x] < 0 -> *)
(*            sgpr_spec p x (-1) (-1) false true false false true false true false true false. *)

(* Lemma sgprP {R : realDomainType} (p : {poly R}) x : *)
(*   sgpr_spec p x (sgpr p x) (Num.sg p.[x]) (p == 0) (p != 0) (sgpr p x == 0)  *)
(*   (sgpr p x > 0) (sgpr p x < 0) (sgpr p x == 1) (sgpr p x == -1) (sgpr p x >= 0) *)
(*   (sgpr p x <= 0) (p.[x] == 0). *)
(* Proof. *)
(* elim: (size p) {-2}p (erefl (size p)) => {p} [p sp| n ihn p sp]. *)
(*   rewrite /sgpr sp; move/eqP: sp; rewrite size_poly_eq0 => /eqP ->. *)
(*   rewrite horner0 !eq_refl ltrr lerr -eqr_oppLR oppr0 [0 == _]eq_sym oner_eq0. *)
(*   by rewrite sgr0; constructor. *)
(* have pn0 : p != 0 by rewrite -size_poly_eq0 sp. *)
(* rewrite (negbTE pn0) /=. *)
(* case: (boolP (root p x)) => [rootp | nrootp]; last first. *)
(*   rewrite sgprNroot //; case: sgrP=> [/rootP||] H; first by rewrite H in nrootp. *)
(*   + rewrite ltr01 ltr10 ler01 ler10 eq_refl -addr_eq0 -[1+1]/2%:R pnatr_eq0. *)
(*     by rewrite oner_eq0; constructor. *)
(*   rewrite eq_refl ltr0N1 ltrN10 ler0N1 lerN10 ![-1 == _]eq_sym -!addr_eq0. *)
(*   by rewrite add0r -[1+1]/2%:R pnatr_eq0 oner_eq0; constructor. *)
(* have spd : size p^`() = n by rewrite size_deriv sp. *)
(* rewrite sgpr_deriv // -rootE rootp (rootP rootp) sgr0. *)
(* have /eqP := (eq_refl (sgpr p^`() x)); move H : {1}(sgpr _ _) => s. *)
(* have [] := (ihn _ spd); rewrite -H => h1 h2; first last; do 4?by constructor. *)
(* by have := (root_size_gt1 pn0 rootp); rewrite sp -spd h1 size_poly0 ltnn. *)
(* Qed. *)

(* Lemma sgpr_dec {R : realDomainType} (p : {poly R}) (x : R) : *)
(*   {sgpr p x == -1} + {sgpr p x == 1} + {sgpr p x == 0}. *)
(* Proof. *)
(* case: sgprP => [|_ _ _|_ _|_ _ _|_ _]; first by right. *)
(* + by left; right. *)
(* + by left; right. *)
(* + by left; left. *)
(* by left; left. *)
(* Qed. *)

(* Definition sgpl {aR : realDomainType} (p : {poly aR}) x := *)
(*   let fix aux (p : {poly aR}) n := *)
(*   if n is n'.+1 *)
(*     then if ~~ root p x *)
(*       then Num.sg p.[x] *)
(*       else - aux p^`() n' *)
(*     else 0 *)
(*       in aux p (size p). *)

(* Lemma sgpl_map (fR : realFieldType) (aR : realDomainType)  *)
(*   (f : {rmorphism fR -> aR}) (f_mono : {mono f : x y / x <= y >-> x <= y}) p x : *)
(*   sgpl (map_poly f p) (f x) = f (sgpl p x). *)
(* Proof. *)
(* rewrite /sgpl size_map_poly. *)
(* elim: (size p) {1 3}p => {p} [|n ihn p]; first by rewrite rmorph0. *)
(* case: ifP; rewrite fmorph_root ?horner_map => ->; last first. *)
(*   by rewrite deriv_map ihn rmorphN. *)
(* apply/esym; case: sgrP => [-> ||]; first by rewrite rmorph0 sgr0. *)
(*   by rewrite rmorph1 -(lerW_mono f_mono) rmorph0 => /gtr0_sg ->. *)
(* by rewrite rmorphN1 -(lerW_mono f_mono) rmorph0 => /ltr0_sg ->. *)
(* Qed. *)

(* Lemma sgpl_sgpr {R : rcfType} (p : {poly R}) x : *)
(*   sgpl p x = (-1) ^+ (\mu_x p) * sgpr p x. *)
(* Proof. *)
(* rewrite /sgpl /sgpr. *)
(* elim: (size p) {-2}p (erefl (size p)) => {p} [p -> | n ihn p sp]. *)
(*   by rewrite mulr0. *)
(* rewrite sp /=; case: ifP => [/muNroot -> | ]; first by rewrite expr0 mul1r. *)
(* move/negbT/negPn => Hroot. *)
(* have spd : size p^`() = n by rewrite size_deriv sp. *)
(* rewrite -spd (ihn _ spd) (mu_deriv_root _ Hroot) -?size_poly_eq0 ?sp //. *)
(* by rewrite addn1 exprS mulN1r mulNr. *)
(* Qed. *)

(* Lemma sgpl_deriv (R : realDomainType) (p : {poly R}) (x : R) : *)
(*   root p x -> sgpl p x = - sgpl p^`() x. *)
(* Proof. *)
(* rewrite /sgpl. *)
(* elim: (size p) {-2}p (erefl (size p)) x => {p} [p |n ihn p sp x]. *)
(*   move/eqP; rewrite size_poly_eq0. *)
(*   by move/eqP => -> x _; rewrite deriv0 size_poly0 oppr0. *)
(* by rewrite /sgpl size_deriv sp /= => -> /=. *)
(* Qed. *)

(* Lemma sgplNroot (R : realDomainType) (p : {poly R}) (x : R) : *)
(*   ~~ root p x -> sgpl p x = Num.sg p.[x]. *)
(* Proof. *)
(* case: (boolP (p == 0)) => [/eqP -> | pn0 rootNpx]; first by rewrite root0. *)
(* rewrite /sgpl; suff -> : size p = (size p^`()).+1 by rewrite rootNpx. *)
(* by rewrite size_deriv prednK // size_poly_gt0. *)
(* Qed. *)

(* (* :TODO: modif in sgp_right_eq0 *) *)
(* Lemma sgpl_eq0 (R : realDomainType) p (x : R) : (sgpl p x == 0) = (p == 0). *)
(* Proof. *)
(* case: (altP (p =P 0))=> [->|p0]; first by rewrite /sgpl size_poly0 eq_refl. *)
(* rewrite /sgpl. *)
(* elim: (size p) {-2}p (erefl (size p)) p0=> {p} [|sp ihsp] p esp p0. *)
(*   by move/eqP:esp; rewrite size_poly_eq0 (negPf p0). *)
(* rewrite esp /=; case px0: root=> //=; rewrite ?sgr_cp0 ?px0// oppr_eq0. *)
(* have hsp: sp = size p^`() by rewrite size_deriv esp. *)
(* rewrite hsp ihsp // -size_poly_eq0 -hsp; apply/negP; move/eqP=> sp0. *)
(* by have := root_size_gt1 p0 px0; rewrite esp sp0 ltnn. *)
(* Qed. *)

(* CoInductive sgpl_spec {R : realDomainType} (p : {poly R}) (x : R) : *)
(*   R -> R -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> bool -> Type := *)
(* | Sgpl0 : p = 0 -> *)
(*            sgpl_spec p x 0 0 true false true false false false false true true true *)
(* | SgplPosR : p != 0 -> root p x -> sgpl p^`() x = -1 -> *)
(*            sgpl_spec p x 1 0 false true false true false true false true false true *)
(* | SgplPosNr : p != 0 -> p.[x] > 0 -> *)
(*            sgpl_spec p x 1 1 false true false true false true false true false false *)
(* | SgplNegR : p != 0 -> root p x -> sgpl p^`() x = 1 -> *)
(*            sgpl_spec p x (-1) 0 false true false false true false true false true true *)
(* | SgplNegNr : p != 0 -> p.[x] < 0 -> *)
(*            sgpl_spec p x (-1) (-1) false true false false true false true false true false. *)

(* Lemma sgplP {R : realDomainType} (p : {poly R}) x : *)
(*   sgpl_spec p x (sgpl p x) (Num.sg p.[x]) (p == 0) (p != 0) (sgpl p x == 0)  *)
(*   (sgpl p x > 0) (sgpl p x < 0) (sgpl p x == 1) (sgpl p x == -1) (sgpl p x >= 0) *)
(*   (sgpl p x <= 0) (p.[x] == 0). *)
(* Proof. *)
(* elim: (size p) {-2}p (erefl (size p)) => {p} [p sp| n ihn p sp]. *)
(*   rewrite /sgpl sp; move/eqP: sp; rewrite size_poly_eq0 => /eqP ->. *)
(*   rewrite horner0 !eq_refl ltrr lerr -eqr_oppLR oppr0 [0 == _]eq_sym oner_eq0. *)
(*   by rewrite sgr0; constructor. *)
(* have pn0 : p != 0 by rewrite -size_poly_eq0 sp. *)
(* rewrite (negbTE pn0) /=. *)
(* case: (boolP (root p x)) => [rootp | nrootp]; last first. *)
(*   rewrite sgplNroot //; case: sgrP=> [/rootP||] H; first by rewrite H in nrootp. *)
(*   + rewrite ltr01 ltr10 ler01 ler10 eq_refl -addr_eq0 -[1+1]/2%:R pnatr_eq0. *)
(*     by rewrite oner_eq0; constructor. *)
(*   rewrite eq_refl ltr0N1 ltrN10 ler0N1 lerN10 ![-1 == _]eq_sym -!addr_eq0. *)
(*   by rewrite add0r -[1+1]/2%:R pnatr_eq0 oner_eq0; constructor. *)
(* have spd : size p^`() = n by rewrite size_deriv sp. *)
(* rewrite sgpl_deriv // -rootE rootp (rootP rootp) sgr0 oppr_eq0 !oppr_cp0 eqr_opp eqr_oppLR. *)
(* have /eqP := (eq_refl (sgpl p^`() x)); move H : {1}(sgpl _ _) => s. *)
(* have [] := (ihn _ spd); rewrite -H ?opprK => h1 h2; first last; do 4?by constructor. *)
(* by have := (root_size_gt1 pn0 rootp); rewrite sp -spd h1 size_poly0 ltnn. *)
(* Qed. *)

(* Lemma sgpl_dec {R : realDomainType} (p : {poly R}) (x : R) : *)
(*   {sgpl p x == -1} + {sgpl p x == 1} + {sgpl p x == 0}. *)
(* Proof. *)
(* case: sgplP => [|_ _ _|_ _|_ _ _|_ _]; first by right. *)
(* + by left; right. *)
(* + by left; right. *)
(* + by left; left. *)
(* by left; left. *)
(* Qed. *)

(* Section SingleRoot. *)

(* (* condition trop forte : racine multiple ? (double) *) *)

(* Definition single_root {R : realDomainType} (p : {poly R}) (a b : R) := *)
(*   let q := psep p in  *)
(*   (forall x, ratr x \in `]a, b[ -> (forall y, ratr y \in `]a, b[ -> *)
(*   Num.sg q.[ratr x] < Num.sg q.[ratr y] -> *)
(*   sgpr q a * (ratr y) < sgpr q a * (ratr x))). *)

(* Lemma single_root0 {R : realDomainType} (a b : R) : *)
(*   single_root 0 a b. *)
(* Proof.  *)
(* by rewrite /single_root => x x_in y y_in; rewrite div0p !horner0 sgr0 ltrr. *)
(* Qed. *)

(* Lemma monoI_in_single_root {R : realDomainType} (p : {poly R}) (a b : R) : *)
(*   {in `]a, b[ &, {mono (horner p) : x y / x <= y >-> x <= y}} -> *)
(*   single_root p a b. *)
(* Proof. *)
(* case: (boolP (p == 0)) => [/eqP -> H | pn0]; first by exact: single_root0. *)
(* move=> H x x_in y y_in /sgr_mono. *)
(* set q := gcdp _ _. *)

(* Lemma single_root_size2 {R : realDomainType} (a b x : R) : *)
(*   x \in `]a, b[ -> single_root ('X - x%:P) a b. *)
(* Proof. *)
(* move=> x_in; rewrite /single_root psep_XsubC. *)
(* rewrite sgprNroot ?sgplNroot ?rootE ?hornerXsubC ?subr_eq0; first last;  *)
(*   do 2? by rewrite neqr_lt (itvP x_in) ?orbT //. *)
(* rewrite ltr0_sg ?subr_lt0 ?gtr0_sg ?subr_gt0 ?(itvP x_in) //. *)
(* move=> u u_in v v_in; rewrite !hornerXsubC (ltr_nmul2l (@ltrN10 _)). *)
(* by move/sgr_mono; rewrite ltr_add2r. *)
(* Qed. *)

(* Lemma single_root_ge {R : realDomainType} (p : {poly R}) a b : *)
(*   b <= a -> single_root p a b. *)
(* Proof.  *)
(* by move=> le_ba; rewrite /single_root => x /itvP /= x_in; rewrite x_in in le_ba. *)
(* Qed. *)


(* Lemma single_root_map (p : {poly rat}) a b (R : realFieldType) : *)
(*   single_root p a b <-> single_root (map_poly (@ratr R) p) (ratr a) (ratr b). *)
(* Proof. *)
(* rewrite /single_root. *)
(* split=> H x x_in y y_in.  *)
(* + have:= (H x _ y _); rewrite -!(fmorph_eq_rat (GRing.idfun_rmorphism _)) => h. *)
(*   rewrite -psep_map (sgpr_map (@ler_rat R)) /= -!rmorphM !horner_map -!ratr_sg. *)
(*   rewrite 2!ltr_rat; apply: h => /=; apply/itv_dec. *)
(*     by have /itv_dec := x_in; rewrite /= ?ltr_rat. *)
(*   by have /itv_dec := y_in; rewrite /= ?ltr_rat. *)
(* move: x_in y_in; rewrite -!(fmorph_eq_rat (GRing.idfun_rmorphism _)) /=. *)
(* move=> x_in y_in; have:= (H x _ y _); rewrite -psep_map !horner_map -!ratr_sg. *)
(* rewrite (sgpr_map (@ler_rat R)) -!rmorphM 2!ltr_rat. *)
(* by apply; apply/itv_dec => /=; rewrite !ltr_rat ?(itvP x_in) ?(itvP y_in). *)
(* Qed. *)

(* Lemma single_rootN {R : realFieldType} (p : {poly R}) a b : *)
(*   single_root (-p) a b <-> single_root p a b. *)
(* Proof. by rewrite /single_root psepN. Qed. *)

(* Lemma single_rootP {R : rcfType} (p : {poly R}) a b : *)
(*   reflect (single_root p a b) (size (roots p a b) <= 1)%N. *)
(* Proof. *)
(* case: (boolP (p == 0)) => [/eqP -> | pn0]. *)
(*   by rewrite roots0 /=; apply/ReflectT/single_root0. *)
(* case: (ltrP a b) => [lt_ab | le_ba]; last first. *)
(*   by rewrite (rootsEba _ le_ba) /=; apply/ReflectT/single_root_ge/le_ba. *)
(* apply: (iffP idP) => [{lt_ab} |]. *)
(* + rewrite leq_eqVlt ltnS leqn0 => /orP[| /eqP/size0nil eq_roots]; last first. *)
(*   - have/(roots_nil pn0) := eq_roots => H x x_in y y_in. *)
(*     suff Hz z : z \in `]a, b[ -> Num.sg (psep p).[z] = sgp_right (psep p) a. *)
(*       by rewrite !Hz ?ltrr. *)
(*     move=> z_in; apply: (@sgr_neighpr _ b); rewrite /neighpr /next_root. *)
(*     by rewrite psep_eq0 (negbTE pn0) psep_roots eq_roots maxr_l ?(itvP z_in). *)
(*   rewrite -psep_roots; move eq_s: (roots (psep p) a b) => s. *)
(*   case: s eq_s => [eq0 //= | u s eqs].  *)
(*   rewrite /= eqSS size_eq0 => /eqP eq0; move/eqP : eqs; rewrite eq0 => {s eq0}. *)
(*   rewrite roots_cons => /and5P[psn0 u_in /eqP rau rootu /eqP rub]. *)
(*   have Hinf z : z \in `]a, b[ ->  *)
(*     ((Num.sg (psep p).[z] == sgpr (psep p) a) = (z < u)) *  *)
(*     ((Num.sg (psep p).[z] == 0) = (z == u)) *  *)
(*     ((Num.sg (psep p).[z] == - sgpr (psep p) a) = (u < z)). *)
(*     move=> z_in; case: (ltrgtP z u) => [lt_zu | lt_uz | eq_uz]; last first. *)
(*     + rewrite eq_uz; move/rootP : rootu => ->; rewrite sgr0 eq_refl -eqr_oppLR. *)
(*       by rewrite oppr0 eq_sym sgpr_eq0 (negbTE psn0). *)
(*     + rewrite (@sgr_neighpr _ b _ u) ?sgpr_sgp_right; last first. *)
(*         rewrite /neighpr /next_root rub (negbTE psn0) maxr_l /= ?(itvP u_in) //. *)
(*         by rewrite inE ?(itvP z_in) lt_uz. *)
(*       rewrite -(@sgr_neighpr _ u _ a ((a + u)/2%:R)); last first. *)
(*         rewrite /neighpr /next_root rau /= (negbTE psn0) maxr_l ?(itvP u_in) //. *)
(*         by rewrite mid_in_itvoo ?(itvP u_in). *)
(*       rewrite (@sgr_neighpl _ a (psep p) u); last first. *)
(*         rewrite /neighpl /prev_root rau /= (negbTE psn0) minr_l ?(itvP u_in) //. *)
(*         by rewrite mid_in_itvoo ?(itvP u_in). *)
(*       rewrite (psep_mu_root pn0) /=; last by rewrite -psep_root. *)
(*       rewrite expr1 mulN1r opprK eq_refl -addr_eq0 -mulr2n mulrn_eq0 /=. *)
(*       by rewrite sgp_right_eq0 (negbTE psn0). *)
(*     rewrite (@sgr_neighpr _ u _ a); last first. *)
(*       rewrite /neighpr /next_root rau /= (negbTE psn0) maxr_l ?(itvP u_in) //. *)
(*       by rewrite inE ?(itvP z_in) lt_zu. *)
(*     by rewrite -addr_eq0 -mulr2n mulrn_eq0 sgp_right_eq0 (negbTE psn0) eq_refl. *)
(*   move => x x_in y y_in. *)
(*   have [[rlx rex] rgx] := (Hinf _ x_in); have [[rly rey] rgy] := (Hinf _ y_in). *)
(*   have [[h | h]|]:= sgpr_dec (psep p) a; last by rewrite sgpr_eq0 (negbTE psn0). *)
(*   + move/sgr_pair => [[/andP[]|/andP[]]|/andP[]]; move/eqP: h => h. *)
(*     - by rewrite -h rlx rey h => ltxu /eqP ->; rewrite ltr_nmul2l ?ltrN10 ?ltxu. *)
(*     - by rewrite rex => /eqP ->; rewrite ltr_nmul2l ?h ?ltrN10 // -rgy h opprK. *)
(*     rewrite -h rlx ltr_nmul2l ?h ?ltrN10 // => ltxu H. *)
(*     by apply: (ltr_trans ltxu); rewrite -rgy h opprK. *)
(*   move/sgr_pair => [[/andP[]|/andP[]]|/andP[]]; move/eqP: h => h. *)
(*   - by rewrite -h rgx rey ltr_pmul2l ?h ?ltr01 // => ltux /eqP ->. *)
(*   - by rewrite rex -h rly ltr_pmul2l ?h ?ltr01 // => /eqP ->. *)
(*   rewrite -h rgx rly ltr_pmul2l ?h ?ltr01 // => ltux ltyu. *)
(*   by exact: (ltr_trans ltyu ltux). *)
(* rewrite /single_root (negbTE pn0) /= lerNgt lt_ab /= => Hsr. *)



(* Search _ sgpr. *)

(*   case: (ltrgtP (ratr x) u) => [ltxu | ltux | equx]. *)
(*   + have := ltxu; rewrite -rlx; have [[]|] := sgpr_dec (psep p) a; first last. *)
(*     - by rewrite sgpr_eq0 (negbTE psn0). *)
(*     - by move/eqP => ->; move/eqP => ->; case: sgrP_comp. *)
(*     move/eqP => hsgpr; rewrite hsgpr; move/eqP ->; case: sgrP_comp => // H _. *)
(*       rewrite ltr_nmul2l ?ltrN10 //; apply: (ltr_le_trans ltxu). *)
(*       suff : ratr y == u by move/eqP => <-; rewrite lerr. *)
(*       by rewrite -rey sgr_eq0 H. *)
(*    rewrite ltr_nmul2l ?ltrN10 //; apply: (ltr_trans ltxu). *)
(*    by rewrite -rgy hsgpr opprK (gtr0_sg H). *)
(*  + have := ltux; rewrite -rgx; have [[]|] := sgpr_dec (psep p) a; first last. *)
(*    - by rewrite sgpr_eq0 (negbTE psn0). *)
(*    - Focus 2.  *)
(*      by move/eqP => ->; move/eqP => ->; rewrite opprK; case: sgrP_comp. *)
(*    move/eqP => -> *)


(* Search _ (_ == _) (_ <= _) in ssrnum. *)




(*  rewrite -?rlx -?rgx. *)
(*   + case: sgrP_comp. *)
  

(*   case: (sgpr_dec (psep p) a) => [[]|] /eqP hsg; rewrite hsg ?mul1r; last first. *)
(*   + by move/eqP: hsg; rewrite sgpr_eq0 (negbTE psn0). *)
(*   + move: pxy; case: sgrP; case: sgrP_comp => //. *)

(*   rewrite (ltr_nmul2l (@ltrN10 _)). *)
(* Search _ (_ * _) (_ < _) in ssrnum. *)


(*   move: Hinf Hsup; case: sgprP => h; first by rewrite h eq_refl in psn0. *)
(*   +  *)
  
(*   case: (ltrgtP (ratr x) u) => [lt_xu | /eqP eq_xu | lt_ux]. *)
(*   + have eq_x := (Hinf _ x_in lt_xu). *)

(*   - have := (@sgr_neighpr _ u (psep p) a (ratr x)). ; last first. *)
(*       by rewrite Hnr; apply/itv_dec; rewrite /= (itvP x_in) lt_xu. *)
(*     case: sgrP. *)
  


(* Search _ sgp_right. *)

(*   have in_neil z : z < u -> z \in `]a, b[ -> z \in neighpl (psep p) a u. *)
(*     move=> ltzu z_in; apply/itv_dec; rewrite /= ltzu /prev_root ifN // rau /=. *)
(*     by rewrite minr_l ?(itvP u_in) ?(itvP z_in). *)
(*   have in_neir z : z > u -> z \in `]a, b[ -> z \in neighpr (psep p) u b. *)
(*     move=> ltuz z_in; apply/itv_dec; rewrite /= ltuz /next_root ifN // rub /=. *)
(*     by rewrite maxr_l ?(itvP u_in) ?(itvP z_in). *)
(*   rewrite /single_root (itvP u_in) => x x_in y y_in. *)
(*   wlog : x y x_in y_in / (@ratr R) x < ratr y. *)
(*     case: (ltrgtP (@ratr R x) (ratr y)) => [ltxy | ltyx | eqxy]. *)
(*     + by move/(_ x y x_in y_in ltxy). *)
(*     + move/(_ y x y_in x_in ltyx)/eqP/(congr1 -%R). *)
(*       by rewrite -sgrN opprB => ->; rewrite -mulrN -sgrN opprB. *)
(*     by move=> _; rewrite !eqxy !subrr sgr0 mulr0. *)
(*   move=> ltxy; have -> : @Num.sg R (ratr x - ratr y) = -1. *)
(*     by apply/ltr0_sg; rewrite subr_lt0. *)
(*   case: (ltrgtP (ratr x) u) => [ltxu | ltux | eqxu]; last first. *)
(*   + rewrite eqxu in ltxy; have -> := (sgr_neighpr (in_neir _ ltxy y_in)). *)
(*     rewrite !sgpr_sgp_right eqxu (rootP rootu) sgr0 sub0r sgrN mulrN1 eqr_opp. *)
(*     Focus 2. *)
    
(* Search _ roots_on. *)

(* Print neighpr. *)
(* Search _ sgp_right. *)

(* have /negbTE -> := pn0. *)

(* have:= pn0; case: (p == 0) => //  _. *)

(* polyrN0_itv: *)
(*   forall (R : rcfType) (i : interval R) (p : {poly R}), *)
(*   {in i, forall x : R, ~~ root p x} -> *)
(*   forall y x : R, y \in i -> x \in i -> Num.sg p.[x] = Num.sg p.[y] *)
(* Search _ negb. *)
(* Search _ (_ = false). *)
(* Print negb. *)
(* Print neighpr. *)

(* sgr_neighpl_same: *)
(*   forall (R : rcfType) (p : {poly R}) (a x : R), *)
(*   {in neighpl p a x &, forall y z : R, Num.sg p.[y] = Num.sg p.[z]} *)
(* sgr_neighpr: *)
(*   forall (R : rcfType) (b : R) (p : {poly R}) (x : R), *)
(*   {in neighpr p x b, forall y : R, Num.sg p.[y] = sgp_right p x} *)
(* sgr_neighpr_same: *)
(*   forall (R : rcfType) (p : {poly R}) (x b : R), *)
(*   {in neighpr p x b &, forall y z : R, Num.sg p.[y] = Num.sg p.[z]} *)
(* sgr_neighpl: *)
(*   forall (R : rcfType) (a : R) (p : {poly R}) (x : R), *)
(*   {in neighpl p a x, forall y : R, Num.sg p.[y] = (-1) ^+ odd (\mu_x p) * sgp_right p x} *)
(* Search _ Num.sg 1 in ssrnum. *)
(* sgrN: forall (R : realDomainType) (x : R), Num.sg (- x) = - Num.sg x *)

(* Search _ roots. *)
(* Search _ (size _ == 0%N). *)
(* Print size. *)

(* size_poly1P: *)
(*   forall (R : ringType) (p : {poly R}), reflect (exists2 c : R, c != 0 & p = c%:P) (size p == 1) *)
(* root_is_roots: *)
(*   forall (R : rcfType) (p : {poly R}) (a b : R), *)
(*   p != 0 -> forall x : R, x \in `]a, b[ -> root p x = (x \in roots p a b) *)
(* roots_cons: *)
(*   forall (R : rcfType) (p : {poly R}) (a b x : R) (s : seq R), *)
(*   (roots p a b == x :: s) = *)
(*   [&& p != 0, x \in `]a, b[, roots p a x == [::], root p x & roots p x b == s] *)

(* End SingleRoot. *)

(* Section BetterParams. *)

(* Variable T : archiRcfType. *)

(* Section P_eps. *)

(* Variable x : T. *)
(* Variable p : {poly rat}. *)

(* Definition P_eps : rat := *)
(*   if (((map_poly ratr p).[x] > 0) =P true) is (ReflectT lt_q'0) *)
(*     then sval (rat_dense (lt_q'0)) *)
(*     else 0. *)

(* Definition P_a : rat := *)
(*   if (((map_poly ratr p) - (ratr P_eps)%:P != 0) =P true)  *)
(*        is ReflectT qn0 *)
(*   then sval (rat_dense (prev_root_lt (ltr_snaddr (ltrN10 _) (lerr x)) qn0)) *)
(*   else 0. *)

(* Definition P_b : rat := *)
(*   if (((map_poly ratr p) - (ratr P_eps)%:P != 0) =P true)  *)
(*        is ReflectT qn0 *)
(*   then sval (rat_dense (next_root_gt (ltr_spaddr ltr01 (lerr x)) qn0)) *)
(*   else 0. *)

(* Section P_eps_cond. *)

(* Hypothesis P_lt_q'0 : (map_poly ratr p).[x] > 0. *)

(* Lemma P_lt_0e : 0 < P_eps. *)
(* Proof. *)
(* rewrite /P_eps; case: eqP => [lt_q'0| /negP]; last by rewrite P_lt_q'0. *)
(* by have /andP[] := (svalP (rat_dense lt_q'0)); rewrite ltr0q. *)
(* Qed. *)

(* Lemma P_lt_eq' : ratr P_eps < (map_poly ratr p).[x]. *)
(* Proof. *)
(* rewrite /P_eps; case: eqP => [lt_q'0| /negP]; last by rewrite P_lt_q'0. *)
(* by have /andP[_] := (svalP (rat_dense lt_q'0)). *)
(* Qed. *)

(* Lemma P_q'e_n0 :  *)
(*   (map_poly ratr p) - (ratr P_eps)%:P != 0 :> {poly T}. *)
(* Proof. *)
(* apply/negP; move/eqP/(congr1 (fun q => q.[x]));rewrite hornerD hornerN !hornerC. *)
(* by move=> H; have := P_lt_eq'; rewrite -subr_gt0 H ltrr. *)
(* Qed. *)
  
(* Lemma P_lt_ax : ratr P_a < x. *)
(* Proof. *)
(* rewrite /P_a; case: eqP => [q_n0| /negP]; last by rewrite P_q'e_n0. *)
(* by move: (prev_root_lt _ _) => H; have /andP[_] := svalP (rat_dense H). *)
(* Qed. *)

(* Lemma P_lt_xb : x < ratr P_b. *)
(* Proof. *)
(* rewrite /P_b; case: eqP => [q_n0| /negP]; last by rewrite P_q'e_n0. *)
(* by move: (next_root_gt _ _) => H; have /andP[] := svalP (rat_dense H). *)
(* Qed. *)

(* Lemma P_lt_ab : P_a < P_b. *)
(* Proof. by have := (ltr_trans P_lt_ax P_lt_xb); rewrite ltr_rat. Qed. *)

(* Lemma P_lt_q' : forall y, P_a <= y <= P_b -> p.[y] > P_eps. *)
(* Proof. *)
(* move=> y /andP[le_ay le_yb]. *)
(* pose q := ((map_poly ratr p) - (ratr P_eps)%:P : {poly T}). *)
(* have Heq s : q.[s] = (map_poly ratr p).[s] - ratr P_eps. *)
(*    by rewrite hornerD hornerN hornerC. *)
(* suff : Num.sg q.[ratr y] = 1. *)
(*   by move/eqP; rewrite sgr_cp0 Heq horner_map subr_gt0 ltr_rat. *)
(* have sgx : Num.sg q.[x] = 1 by apply/gtr0_sg; rewrite Heq subr_gt0 P_lt_eq'. *)
(* have nroot_x : ~~ root q x by rewrite rootE Heq subr_eq0 neqr_lt P_lt_eq' orbT. *)
(* case: (ltrgtP (ratr y) x) => [lt_yx| lt_xy | -> //]. *)
(* + rewrite (@sgr_neighplN _ _ (x - 1) _ nroot_x) ?sgx// /neighpl inE lt_yx andbT. *)
(*   apply/(@ltr_le_trans _ (ratr P_a)); last by rewrite ler_rat le_ay. *)
(*   rewrite /P_a; case: eqP => [q_n0| /negP]; last by rewrite P_q'e_n0. *)
(*   by move: (prev_root_lt _ _) => H; have /andP[] := svalP (rat_dense H). *)
(* rewrite rootE in nroot_x. *)
(* rewrite (@sgr_neighprN _ _ _ (x + 1) nroot_x) ?sgx// /neighpr inE lt_xy /=.  *)
(* apply/(@ler_lt_trans _ (ratr P_b)); first by rewrite ler_rat le_yb. *)
(* rewrite /P_b; case: eqP => [q_n0| /negP]; last by rewrite P_q'e_n0. *)
(* by move: (next_root_gt _ _) => H; have /andP[] := svalP (rat_dense H). *)
(* Qed. *)

(* Lemma P_int_lt0 {fT : rcfType} (y : fT) : *)
(*   y \in `](ratr P_a), (ratr P_b)[ -> 0 < (map_poly ratr p).[y]. *)
(* Proof. *)
(* rewrite inE /= => /andP[lt_ay lt_yb]. *)
(* by apply/(map_poly_pos P_lt_0e P_lt_q'); rewrite (ltrW lt_ay) (ltrW lt_yb). *)
(* Qed. *)

(* End P_eps_cond. *)

(* End P_eps. *)

(* Section BP_Defs. *)

(* Variable x : T. *)
(* Variable p : {poly rat}. *)

(* (* Lemma P_int_neq0 {fT : rcfType} (y : fT) : *) *)
(* (*   (map_poly ratr p).[x] != 0 ->  *) *)
(* (*   y \in `](ratr (P_a x p)), (ratr (P_b x p))[ -> *) *)
(* (*   y \in `](ratr (P_a x (-p))), (ratr (P_b x (-p)))[ ->               *) *)
(* (*   (map_poly ratr p).[y] != 0. *) *)
(* (* Proof. *) *)
(* (* move=> H; case: (boolP ((map_poly ratr p).[x] > 0)) => [H1 H2 | ]. *) *)
(* (*   by have /gtr_eqF -> := P_int_lt0 H1 H2. *) *)
(* (* rewrite -lerNgt ler_eqVlt (negbTE H) orFb -lter_oppE oppr0 -hornerN -rmorphN /=. *) *)
(* (* move/(P_int_lt0)/(_ fT y); rewrite rmorphN hornerN lter_oppE /= neqr_lt. *) *)
(* (* by move => H1 _ H3; rewrite (H1 H3). *) *)
(* (* Qed. *) *)

(* Section Def. *)

(* Definition BP_poly : {poly rat} := *)
(*   if ((p != 0) && (root (map_poly ratr p) x)) *)
(*     then let q := p %/ (gcdp p p^`()) in *)
(*          if ((map_poly ratr q)^`().[x] > 0) *)
(*            then q *)
(*            else -q *)
(*     else 0. *)

(* Definition BP_eps := P_eps x BP_poly^`(). *)
(* Definition BP_a := P_a x BP_poly^`(). *)
(* Definition BP_b := P_b x BP_poly^`(). *)

(* End Def. *)

(* Section Lemmas. *)

(* Hypothesis pn0 : p != 0. *)
(* Hypothesis root_p : root (map_poly ratr p) x. *)

(* Lemma BP_poly_neq0 : BP_poly != 0. *)
(* Proof. *)
(* rewrite /BP_poly pn0 root_p /=. *)
(* have H : p %/ gcdp p p^`() != 0 by rewrite dvdp_div_eq0 ?dvdp_gcdl ?p_neq0. *)
(* by case: ifP => _ //; rewrite oppr_eq0. *)
(* Qed. *)

(* Lemma BP_separable : separable_poly BP_poly. *)
(* Proof. *)
(* rewrite /BP_poly pn0 root_p /=; case: ifP => _. *)
(*   by apply/make_separable/pn0. *)
(* have : (- (p %/ gcdp p p^`()) %| p %/ gcdp p p^`()) by rewrite -dvdp_opp dvdpp. *)
(* by move/dvdp_separable; apply; apply/make_separable/pn0. *)
(* Qed. *)

(* (* :TODO: even longer than before (cf other dev or better_params) *) *)
(* Lemma BP_root {fT : realFieldType} (y : fT) :  *)
(*   root (map_poly ratr p) y = root (map_poly ratr BP_poly) y. *)
(* Proof. *)
(* apply/idP/idP; last first. *)
(*   rewrite /BP_poly pn0 root_p /= => H1. *)
(*   have H : root (map_poly ratr (p %/ gcdp p p^`())) y. *)
(*     by move: H1; case: ifP => _ //; rewrite rmorphN rootN /=. *)
(*   by rewrite -(divpK (dvdp_gcdl p p^`())) rmorphM /= rootM H. *)
(* move=> rooty; rewrite /BP_poly pn0 root_p /=. *)
(* suff H : root (map_poly ratr (p %/ gcdp p p^`())) y. *)
(*   by case: ifP => _ //; rewrite rmorphN rootN /=. *)
(* rewrite map_divp gcdp_map -deriv_map /= -mu_gt0; set q := gcdp _ _; last first. *)
(*   by rewrite (dvdp_div_eq0 (dvdp_gcdl _ _)) map_poly_eq0 pn0. *)
(* have H : ((map_poly ratr p) != 0 :> {poly fT}) by rewrite map_poly_eq0 pn0. *)
(* have := H; rewrite -[X in X != 0](divpK (dvdp_gcdl _ (map_poly ratr p)^`())). *)
(* move/(mu_mul y); rewrite (divpK (dvdp_gcdl _ _)) mu_gcdp; last first. *)
(*   apply/mulf_neq0; first by rewrite map_poly_eq0 pn0. *)
(*   rewrite -size_poly_eq0 -lt0n size_deriv /= -subn1 subn_gt0. *)
(*   by apply/(root_size_gt1 _ rooty); rewrite map_poly_eq0 pn0. *)
(* move/eqP; rewrite -/q (mu_deriv_root H rooty) -[X in minn _ X]addn0.  *)
(* by rewrite -addn_minr minn0 addn0 addnC eqn_add2r eq_sym => /eqP ->. *)
(* Qed.  *)

(* Lemma BP_rootx : root (map_poly ratr BP_poly) x. *)
(* Proof. by rewrite -BP_root root_p. Qed. *)

(* Lemma BP_lt_q'0 : (map_poly ratr BP_poly^`()).[x] > 0. *)
(* Proof. *)
(* have:= BP_rootx; rewrite -deriv_map /BP_poly pn0 root_p; case: ifP=> //= /negbT. *)
(* rewrite -lerNgt ler_eqVlt => /orP[]; last first. *)
(*   by rewrite rmorphN derivN hornerN ltr_oppr oppr0. *)
(* rewrite -rootE deriv_map /= rmorphN rootN /=; set q := _ %/ _ => root_q' root_q. *)
(* have : map_poly ratr p != 0 :> {poly T} by rewrite map_poly_eq0. *)
(* move/make_separable; rewrite /separable_poly -/q. *)
(* rewrite deriv_map -gcdp_map -map_divp /= -/q => /coprimep_root /(_ root_q). *)
(* by rewrite -rootE deriv_map root_q'. *)
(* Qed. *)

(* Lemma BP_lt_ax : ratr BP_a < x. *)
(* Proof. exact: (P_lt_ax BP_lt_q'0). Qed. *)

(* Lemma BP_lt_xb : x < ratr BP_b. *)
(* Proof. exact: (P_lt_xb BP_lt_q'0). Qed. *)

(* Lemma BP_int_deriv {fT : rcfType} (y : fT) : *)
(*   y \in `](ratr BP_a), (ratr BP_b)[ -> 0 < (map_poly ratr BP_poly)^`().[y]. *)
(* Proof. by rewrite deriv_map; apply: (P_int_lt0 BP_lt_q'0). Qed. *)

(* Lemma BP_ltx_p0 y : ratr BP_a <= y -> y < x -> (map_poly ratr BP_poly).[y] < 0. *)
(* Proof. *)
(* move=> le_ay lt_yx; have /deriv_sign_proper/(_ _ _ _ lt_yx) :=(@BP_int_deriv T). *)
(* have /rootP -> := BP_rootx; rewrite !inE le_ay (ltrW BP_lt_ax) (ltrW BP_lt_xb). *)
(* by apply; rewrite !andbT /=; apply/ltrW/(ltr_trans lt_yx BP_lt_xb). *)
(* Qed. *)

(* Lemma BP_lt_pa0 : BP_poly.[BP_a] < 0. *)
(* Proof. by have := (BP_ltx_p0 (lerr _) BP_lt_ax); rewrite horner_map ltrq0. Qed. *)

(* Lemma BP_ltx_0p y : y <= ratr BP_b -> x < y -> 0 < (map_poly ratr BP_poly).[y]. *)
(* Proof. *)
(* move=> le_yb lt_xy; have /deriv_sign_proper/(_ _ _ _ lt_xy):=(@BP_int_deriv T). *)
(* have /rootP -> := BP_rootx; rewrite !inE le_yb (ltrW BP_lt_ax) (ltrW BP_lt_xb). *)
(* by apply; rewrite !andbT /=; apply/ltrW/(ltr_trans BP_lt_ax lt_xy).  *)
(* Qed. *)

(* Lemma BP_lt_0pb : 0 < BP_poly.[BP_b]. *)
(* Proof. by have := (BP_ltx_0p (lerr _) BP_lt_xb); rewrite horner_map ltr0q. Qed. *)

(* Lemma BP_int_p0 {fT : rcfType} :  *)
(*   (0 : fT) \in `](map_poly ratr BP_poly).[ratr BP_a],  *)
(*                     (map_poly ratr BP_poly).[ratr BP_b][. *)
(* Proof. by rewrite inE !horner_map ltrq0 ltr0q BP_lt_pa0 BP_lt_0pb. Qed. *)

(* Lemma BP_lt_ab_fT {fT : rcfType} : ratr BP_a < ratr BP_b :> fT. *)
(* Proof. by rewrite ltr_rat (P_lt_ab BP_lt_q'0). Qed. *)

(* Lemma BP_xroots : *)
(*   roots (map_poly ratr BP_poly) (ratr BP_a) (ratr BP_b) = [:: x]. *)
(* Proof. *)
(* apply/esym/roots_uniq; rewrite ?map_poly_eq0 ?BP_poly_neq0 // /roots_on =>y. *)
(* rewrite !inE; case: (boolP (y > ratr BP_a)) => [lt_ay | ] /=; last first. *)
(*   by rewrite -lerNgt; move=> H; apply/esym/ltr_eqF/(ler_lt_trans H)/BP_lt_ax. *)
(* case: (boolP (y < ratr BP_b)) => [lt_yb | ] /=; last first. *)
(*   by rewrite -lerNgt; move=> H; apply/esym/gtr_eqF/(ltr_le_trans _ H)/BP_lt_xb. *)
(* case: (ltrgtP y x) => [lt_yx | lt_xy | ->]; last by rewrite -BP_root. *)
(*   by rewrite rootE; apply/ltr_eqF/(BP_ltx_p0 _ lt_yx)/ltrW/lt_ay. *)
(* by rewrite rootE; apply/gtr_eqF/(BP_ltx_0p _ lt_xy)/ltrW/lt_yb. *)
(* Qed. *)

(* End Lemmas. *)

(* Variable fT : rcfType. *)

(* Section BP_valDef. *)

(* Definition BP_val : fT := *)
(*   if ((p != 0) =P true, (root (map_poly ratr p) x) =P true) *)
(*        is (ReflectT pn0, ReflectT rootp) *)
(*   then sval (derp_root (BP_int_deriv pn0 rootp)  *)
(*                        (ltrW (BP_lt_ab_fT pn0 rootp)) (BP_int_p0 pn0 rootp)) *)
(*   else 0. *)

(* End BP_valDef. *)

(* Section BP_valLemmas. *)

(* Hypothesis pn0 : p != 0. *)
(* Hypothesis rootp : root (map_poly ratr p) x. *)

(* Lemma BP_lt_av : ratr BP_a < BP_val. *)
(* Proof. *)
(* rewrite /BP_val; case: eqP; last by rewrite pn0.  *)
(* case: eqP; last by rewrite rootp. *)
(* by move=> p0 pr; move: (derp_root _ _ _) => H; have [_ _ /andP[]]:= svalP H. *)
(* Qed. *)

(* Lemma BP_lt_vb : BP_val < ratr BP_b. *)
(* Proof. *)
(* rewrite /BP_val; case: eqP; last by rewrite pn0.  *)
(* case: eqP; last by rewrite rootp. *)
(* by move=> p0 pr; move: (derp_root _ _ _) => H; have [_ _ /andP[]]:= svalP H. *)
(* Qed. *)

(* Lemma BP_rootv : root (map_poly ratr BP_poly) BP_val. *)
(* Proof. *)
(* rewrite /BP_val; case: eqP; last by rewrite pn0.  *)
(* case: eqP; last by rewrite rootp. *)
(* by move=> p0 pr; move: (derp_root _ _ _) => H; have [_ /rootP ->] := svalP H. *)
(* Qed. *)

(* Lemma BP_ltv_p0 y :  *)
(*   ratr BP_a <= y -> y < BP_val -> (map_poly ratr BP_poly).[y] < 0. *)
(* Proof. *)
(* move=> le_ay; rewrite /BP_val; case: eqP; last by rewrite pn0. *)
(* case: eqP; last by rewrite rootp. *)
(* move=> p0 pr; move: (derp_root _ _ _) => H lt_yv. *)
(* by have [H1 _ _ _] := svalP H; have := (H1 y); rewrite inE lt_yv le_ay; apply. *)
(* Qed. *)

(* Lemma BP_ltv_0p y :  *)
(*   y <= ratr BP_b -> BP_val < y -> 0 < (map_poly ratr BP_poly).[y]. *)
(* Proof. *)
(* move=> le_yb; rewrite /BP_val; case: eqP; last by rewrite pn0. *)
(* case: eqP; last by rewrite rootp. *)
(* move=> p0 pr; move: (derp_root _ _ _) => H lt_vy. *)
(* by have [_ _ _] := svalP H; move/(_ y); rewrite inE lt_vy le_yb; apply. *)
(* Qed. *)

(* Lemma BP_lt_inf (q : rat) : (ratr q < BP_val) = (ratr q < x). *)
(* Proof. *)
(* case: (boolP (q < BP_a)) => [lt_qa | ]. *)
(*   apply/idP/idP => _. *)
(*     by apply/(ltr_trans _ (BP_lt_ax _ _)); rewrite // ltr_rat lt_qa. *)
(*   by apply/(ltr_trans _ BP_lt_av); rewrite ltr_rat lt_qa. *)
(* rewrite -lerNgt => le_aq; apply/idP/idP => [lt_qv | lt_qx]. *)
(*   have := (ltr_trans lt_qv BP_lt_vb); rewrite ltr_rat -(ltr_rat T) => lt_qb. *)
(*   have := le_aq; rewrite -(ler_rat fT) => /BP_ltv_p0 /(_ lt_qv) BPq_lt0. *)
(*   case: (ltrgtP) => [lt_xq|//|eq_xq]. *)
(*     have := BP_ltx_0p pn0 rootp (ltrW lt_qb) lt_xq; rewrite ltrNge.  *)
(*     by have := (ltrW BPq_lt0); rewrite !horner_map !lerq0 => ->. *)
(*   have := (BP_rootx pn0 rootp); rewrite rootE eq_xq. *)
(*   by have := (ltr_eqF BPq_lt0); rewrite !horner_map !fmorph_eq0 => ->. *)
(* have := (ltr_trans lt_qx (BP_lt_xb pn0 rootp)); rewrite ltr_rat -(ltr_rat fT). *)
(* move=> lt_qb; have := le_aq; rewrite -(ler_rat T) => /(BP_ltx_p0 pn0 rootp). *)
(* move=> /(_ lt_qx) BPq_lt0; case: (ltrgtP) => [lt_vq|//|eq_vq]. *)
(*   have := BP_ltv_0p (ltrW lt_qb) lt_vq; rewrite ltrNge. *)
(*   by have := (ltrW BPq_lt0); rewrite !horner_map !lerq0 => ->. *)
(* have := BP_rootv; rewrite rootE eq_vq. *)
(* by have /ltr_eqF := BPq_lt0; rewrite !horner_map !fmorph_eq0 => ->. *)
(* Qed. *)

(* Lemma BP_lt_sup (q : rat) : (BP_val < ratr q) = (x < ratr q). *)
(* Proof. *)
(* case: (boolP (q > BP_b)) => [lt_bq | ]. *)
(*   apply/idP/idP => _. *)
(*     by apply/(ltr_trans (BP_lt_xb _ _)); rewrite // ltr_rat lt_bq. *)
(*   by apply/(ltr_trans BP_lt_vb); rewrite ltr_rat lt_bq. *)
(* rewrite -lerNgt => le_qb; apply/idP/idP => [lt_vq | lt_xq]. *)
(*   have := (ltr_trans BP_lt_av lt_vq); rewrite ltr_rat -(ltr_rat T) => lt_aq. *)
(*   have := le_qb; rewrite -(ler_rat fT) => /BP_ltv_0p /(_ lt_vq) BPq_lt0. *)
(*   case: (ltrgtP) => [lt_qx|//|eq_qx]. *)
(*     have := BP_ltx_p0 pn0 rootp (ltrW lt_aq) lt_qx; rewrite ltrNge. *)
(*     by have := (ltrW BPq_lt0); rewrite !horner_map !ler0q => ->. *)
(*   have := (BP_rootx pn0 rootp); rewrite rootE -eq_qx. *)
(*   by have := (gtr_eqF BPq_lt0); rewrite !horner_map !fmorph_eq0 => ->. *)
(* have := (ltr_trans (BP_lt_ax pn0 rootp) lt_xq); rewrite ltr_rat -(ltr_rat fT). *)
(* move=> lt_aq; have := le_qb; rewrite -(ler_rat T) => /(BP_ltx_0p pn0 rootp). *)
(* move=> /(_ lt_xq) BPq_lt0; case: (ltrgtP) => [lt_qv|//|eq_qv]. *)
(*   have := BP_ltv_p0 (ltrW lt_aq) lt_qv; rewrite ltrNge. *)
(*   by have := (ltrW BPq_lt0); rewrite !horner_map !ler0q => ->.  *)
(* have := BP_rootv; rewrite rootE -eq_qv. *)
(* by have /gtr_eqF := BPq_lt0; rewrite !horner_map !fmorph_eq0 => ->. *)
(* Qed. *)

(* Lemma BP_val_eq (y : fT) :  *)
(*   (BP_val == y) =  *)
(*   ((ratr BP_a < y < ratr BP_b) && root (map_poly ratr BP_poly) y). *)
(* Proof. *)
(* apply/eqP/andP => [<- | [/andP[]]]; first by rewrite BP_lt_av BP_lt_vb BP_rootv. *)
(* move=> lt_ay lt_yb rooty. *)
(* have y_in : y \in `](ratr BP_a), (ratr BP_b)[ by rewrite inE lt_ay lt_yb. *)
(* have []:= (@monotonic_rootN fT (map_poly ratr BP_poly) (ratr BP_a) (ratr BP_b)). *)
(* + move=> z /(BP_int_deriv pn0 rootp); rewrite rootE neqr_lt => ->. *)
(*   by rewrite orbT. *)
(* + by move/roots_on_nil/(_ y y_in); rewrite rooty. *)
(* move=> [z /roots_onP H]; have := (H y y_in); rewrite rooty /= inE => /esym /eqP. *)
(* have : BP_val \in `](ratr BP_a), (ratr BP_b)[ by rewrite inE BP_lt_av BP_lt_vb. *)
(* by move/H; rewrite BP_rootv /= inE; move/esym/eqP => -> ->. *)
(* Qed. *)

(* Lemma BP_vroots : *)
(*   roots (map_poly ratr BP_poly) (ratr BP_a) (ratr BP_b) = [:: BP_val]. *)
(* Proof. *)
(* apply/esym/roots_uniq; rewrite ?map_poly_eq0 ?BP_poly_neq0 //. *)
(* by rewrite /roots_on => y; rewrite !inE eq_sym BP_val_eq. *)
(* Qed. *)

(* Lemma BP_valP (y : fT) : *)
(*   reflect ((forall qa qb : rat, (ratr qa < x < ratr qb) ->  *)
(*                                 (ratr qa < y < ratr qb)) /\ *)
(*            (root (map_poly ratr p) y))  *)
(*           (BP_val == y). *)
(* Proof. *)
(* apply (iffP idP) => [/eqP H | ].  *)
(*   split; rewrite -H ; first by move=> qa qb; rewrite ?BP_lt_inf ?BP_lt_sup. *)
(*   by rewrite BP_root ?BP_rootv. *)
(* move=> [Hint Hroot]; rewrite BP_val_eq Hint -?BP_root ?Hroot //. *)
(* by rewrite -BP_lt_inf -BP_lt_sup BP_lt_av BP_lt_vb. *)
(* Qed. *)

(* End BP_valLemmas. *)

(* End BP_Defs. *)

(* Section BP_morph. *)

(* Variable fT : rcfType. *)

(* Lemma BP_val_root (x : T) (p q : {poly rat}) : *)
(*   p != 0 -> root (map_poly ratr p) x -> *)
(*   root (map_poly ratr q) x ->  *)
(*   root (map_poly ratr q) (BP_val x p fT). *)
(* Proof. *)
(* move=> pn0 rootpx rootqx; set v := BP_val _ _ _. *)
(* case: (boolP (q == 0)) => [/eqP -> | qn0]; first by rewrite map_poly0 root0. *)
(* pose r := (gcdp (BP_poly x p) q). *)
(* have rootr : root (map_poly ratr r) x. *)
(*   by rewrite gcdp_map root_gcd /= rootqx -BP_root ?rootpx ?pn0. *)
(* suff : root (map_poly ratr r) v by rewrite gcdp_map root_gcd /= => /andP[]. *)
(* have := (divpK (dvdp_gcdl (BP_poly x p) q)); rewrite -/r => eq_BP. *)
(* have := BP_vroots fT pn0 rootpx; rewrite -eq_BP rmorphM mulrC /= => Hm. *)
(* have := BP_separable pn0 rootpx; rewrite -eq_BP separable_mul. *)
(* move=> /andP[BPr_sep /andP[r_sep]]; rewrite coprimep_sym => BPr_cop. *)
(* have x_n0 : (map_poly ratr ((BP_poly x p) %/ r)).[x] != 0. *)
(*   by apply/(coprimep_root _ rootr); rewrite coprimep_map BPr_cop. *)
(* have rn0 : (map_poly ratr r) != 0 :> {poly fT}. *)
(*   by rewrite map_poly_eq0 gcdp_eq0 negb_and qn0 orbT. *)
(* have brn0 : (map_poly ratr ((BP_poly x p) %/ r)) != 0 :> {poly fT}. *)
(*   rewrite map_poly_eq0; apply/negP=> /eqP H. *)
(*   by have := x_n0; rewrite H rmorph0 horner0 eq_refl. *)
(* have := BPr_cop; rewrite -(coprimep_map (@ratr_rmorphism fT)). *)
(* move/(roots_mul_coprime (BP_lt_ab_fT pn0 rootpx) rn0 brn0); rewrite Hm => Hmm. *)
(* suff /negbTE H : ~~ root (map_poly ratr ((BP_poly x p) %/ r)) v. *)
(*   have : v \in [:: v] by rewrite inE. *)
(*   rewrite (perm_eq_mem Hmm) mem_cat.  *)
(*   by rewrite -!root_is_roots ?H ?orbF ?inE ?BP_lt_av ?BP_lt_vb. *)
(* have := x_n0; rewrite rootE !neqr_lt => /orP[| H]; last first. *)
(*   have/P_int_lt0 -> := H; rewrite ?orbT // inE ?BP_lt_inf ?BP_lt_sup //. *)
(*   by rewrite ?P_lt_ax ?P_lt_xb. *)
(* rewrite -[_ < 0]lter_oppE -[_ < 0]lter_oppE -!hornerN -!rmorphN /= => H. *)
(* have/P_int_lt0 -> := H; rewrite //= inE ?BP_lt_inf ?BP_lt_sup //. *)
(* by rewrite ?P_lt_ax ?P_lt_xb. *)
(* Qed. *)

(* Lemma root_BP_val (x : T) (p q : {poly rat}) : *)
(*   p != 0 -> root (map_poly ratr p) x -> *)
(*   root (map_poly ratr q) (BP_val x p fT) -> *)
(*   root (map_poly ratr q) x. *)
(* Proof. *)
(* move=> pn0 rootpx rootqy. *)
(* case: (boolP (q == 0)) => [/eqP -> | qn0]; first by rewrite map_poly0 root0. *)
(* have rootby:= (BP_rootv fT pn0 rootpx). *)
(* have rootry: root (map_poly ratr (gcdp (BP_poly x p) q)) (BP_val x p fT). *)
(*   by rewrite gcdp_map root_gcd /= rootqy rootby. *)
(* have rn0: (gcdp (BP_poly x p) q) != 0 by rewrite gcdp_eq0 negb_and BP_poly_neq0. *)
(* have rootbx:= (BP_rootx pn0 rootpx). *)
(* suff: root (map_poly ratr (gcdp (BP_poly x p) q)) x. *)
(*   by rewrite gcdp_map root_gcd => /andP[_ /=]. *)

(* Search _ gcdp. *)
(* Search _ roots. *)
(* Search _ gdcop. *)
(* Search _ root. *)
(* Search _ roots roots_on. *)
(* Search _ roots. *)
(* Print roots_spec. *)
(* Search _ size 1%N in seq. *)

(* Lemma BP_valpP (x : T) (y : fT) (p q : {poly rat}) : *)
(*   p != 0 -> root (map_poly ratr p) x -> *)
(*   q != 0 -> root (map_poly ratr q) x -> *)
(*   reflect ((forall qa qb : rat, (ratr qa < x < ratr qb) ->  *)
(*                                 (ratr qa < y < ratr qb)) /\ *)
(*            (root (map_poly ratr q) y))  *)
(*           (BP_val x p fT == y). *)
(* Proof. *)
(* move=> pn0 rootpx qn0 rootqx. *)
(* apply (iffP idP) => [Heq |[]]. *)
(*   split; first by have /(BP_valP pn0 rootpx) [] := Heq. *)
(*   by have /eqP <- := Heq; apply: BP_val_root. *)
(* move=> Hrat rootqy. *)
(* have rootbx : root (map_poly ratr (BP_poly x q)) x by rewrite -BP_root. *)
(* have rootby : root (map_poly ratr (BP_poly x q)) y by rewrite -BP_root. *)
(* have rootbv : root (map_poly ratr (BP_poly x q)) (BP_val x p fT). *)
(*   by apply/BP_val_root/rootbx/rootpx/pn0. *)
(* have v_in : (BP_val x p fT) \in `](ratr (BP_a x q)), (ratr (BP_b x q))[. *)
(*   by rewrite inE ?BP_lt_sup ?BP_lt_inf // ?BP_lt_ax ?BP_lt_xb. *)
(* have []:= (@monotonic_rootN fT (map_poly ratr (BP_poly x q))  *)
(*                             (ratr (BP_a x q)) (ratr (BP_b x q))). *)
(* + move=> z /(BP_int_deriv qn0 rootqx); rewrite rootE neqr_lt => ->. *)
(*   by rewrite orbT. *)
(* + by move/roots_on_nil/(_ (BP_val x p fT) v_in); rewrite rootbv. *)
(* move=> [z /roots_onP H]; have :=(H _ v_in); rewrite rootbv /= inE => /esym /eqP. *)
(* have : y \in `](ratr (BP_a x q)), (ratr (BP_b x q))[.  *)
(*   by rewrite inE Hrat ?BP_lt_ax ?BP_lt_xb. *)
(* by move/H; rewrite rootby /= inE; move/esym/eqP => -> ->. *)
(* Qed. *)

(* Variables x y : T. *)
(* Variables p q r : {poly rat}. *)

(* Hypothesis pn0 : p != 0. *)
(* Hypothesis qn0 : q != 0. *)
(* Hypothesis rn0 : r != 0. *)
(* Hypothesis rootpx : root (map_poly ratr p) x. *)
(* Hypothesis rootqy : root (map_poly ratr q) y. *)

(* Lemma BP_val0 (s : {poly rat}) (sn0 : s != 0)  *)
(*       (roots0 : root (map_poly ratr s) (0 : T)) :  *)
(*   BP_val 0 s fT = 0. *)
(* Proof. *)
(* apply/eqP/(BP_valP sn0 roots0); have fT0 := (rmorph0 _ : ratr 0 = 0 :> fT). *)
(* have T0 := (rmorph0 _ : ratr 0 = 0 :> T); split; last first. *)
(*   by have := roots0; rewrite !rootE -fT0 -T0 !horner_map fT0 T0 /= !fmorph_eq0. *)
(* by move=> qa qb; rewrite -fT0 -T0 !ltr_rat. *)
(* Qed. *)

(* Lemma BP_val1 (rootr1 : root (map_poly ratr r) (1 : T)) :  *)
(*   BP_val 1 r fT = 1. *)
(* Proof. *)
(* apply/eqP/(BP_valP rn0 rootr1); have fT1 := (rmorph1 _ : ratr 1 = 1 :> fT). *)
(* have T1 := (rmorph1 _ : ratr 1 = 1 :> T); split; last first. *)
(*   by have := rootr1; rewrite !rootE -fT1 -T1 !horner_map /= !fmorph_eq0. *)
(* by move=> qa qb; rewrite -fT1 -T1 !ltr_rat. *)
(* Qed. *)

(* Lemma BP_valB (rootrxy : root (map_poly ratr r) (x - y)) : *)
(*   (BP_val (x - y) r fT) = (BP_val x p fT) - (BP_val y q fT). *)
(* Proof. *)
(* pose pm := (lead_coef p)^-1 *: p. *)
(* have pmn0 : pm != 0. *)
(*   by rewrite /pm scale_poly_eq0 negb_or invr_eq0 lead_coef_eq0 pn0. *)
(* have rootpmx : root (map_poly ratr pm) x. *)
(*   by rewrite /pm map_polyZ /= rootZ // fmorph_eq0 invr_eq0 lead_coef_eq0 pn0. *)
(* have /eqP -> : BP_val x p fT == BP_val x pm fT. *)
(*   apply/BP_valP => //; split; last by rewrite BP_val_root. *)
(*   by move=> qa qb Hrat; rewrite BP_lt_inf ?BP_lt_sup. *)
(* pose P := polyXY.sub_annihilant pm q. *)
(* have Pn0 : P != 0 by apply: polyXY.sub_annihilant_neq0. *)
(* have rootPxy : root (map_poly ratr P) (x - y). *)
(*   by apply/rootP/polyXY.map_sub_annihilantP => //; apply/rootP. *)
(* apply/eqP/(BP_valpP _ _ _ Pn0 rootPxy) => //; split; last first. *)
(*   by apply/rootP/polyXY.map_sub_annihilantP => //=; apply/rootP/BP_val_root. *)
(* move=> qa qb /andP[lt_qaxy lt_xyqb]. *)
(* pose e := Num.min ((x - y) - ratr qa) (ratr qb - (x - y)). *)
(* have e_gt0 : e / 2%:R > 0.  *)
(*   by rewrite divr_gt0 ?ltr0n // ltr_minr !subr_gt0 lt_qaxy lt_xyqb.  *)
(* have [qe /andP[lt_0qe]] := rat_dense e_gt0. *)
(* rewrite ltr_pdivl_mulr ?ltr0n // mulr_natr mulr2n => lt_qeqee. *)
(* have /rat_dense [qx /andP[]] : x - ratr qe < x. *)
(*   by rewrite ltr_subl_addr ltr_addl lt_0qe.  *)
(* rewrite ltr_subl_addr -rmorphD /= => lt_xq lt_qx. *)
(* have /rat_dense [qy /andP[]] : y - ratr qe < y. *)
(*   by rewrite ltr_subl_addr ltr_addl lt_0qe.  *)
(* rewrite ltr_subl_addr -rmorphD /= => lt_yq lt_qy. *)
(* have lt_qa : ratr qa < ratr qx - ratr (qy + qe) :> fT. *)
(*   rewrite -rmorphB ltr_rat -(ltr_rat T). *)
(*   apply/(@ler_lt_trans _ ((x - y) - e)).  *)
(*     by rewrite ler_subr_addr -ler_subr_addl ler_minl lerr. *)
(*   rewrite addrAC opprD addrA [in ratr _]addrAC rmorphB /=. *)
(*   apply/(ltr_sub _ lt_qy); rewrite ltr_subl_addr -ltr_subl_addl. *)
(*   apply/(ltr_trans _ lt_qeqee); rewrite rmorphB opprB /=. *)
(*   by rewrite addrA ltr_subl_addl addrA ltr_add2r -rmorphD. *)
(* have lt_qb : ratr (qx + qe) - ratr qy < ratr qb :> fT. *)
(*   rewrite -rmorphB ltr_rat -(ltr_rat T). *)
(*   apply/(@ltr_le_trans _ ((x - y) + e)); last first.  *)
(*     by rewrite -ler_subr_addl ler_minl lerr orbT. *)
(*   rewrite -[in ratr _]addrA rmorphD rmorphB /= -addrA; apply/(ltr_add lt_qx). *)
(*   rewrite [-y + e]addrC ltr_subr_addl; apply/(ltr_trans _ lt_qeqee). *)
(*   by rewrite addrA ltr_subl_addl addrA ltr_add2r -rmorphD lt_yq. *)
(* apply/andP; split. *)
(*   by apply/(ltr_trans lt_qa)/ltr_sub; rewrite ?BP_lt_sup ?BP_lt_inf. *)
(* by apply/(ltr_trans _ lt_qb)/ltr_sub; rewrite ?BP_lt_sup ?BP_lt_inf //. *)
(* Qed. *)

(* Lemma BP_valM (rootrxy : root (map_poly ratr r) (x * y)) : *)
(*   (BP_val (x * y) r fT) = (BP_val x p fT) * (BP_val y q fT). *)
(* Proof. *)
(* case: (boolP (y == 0)) => [/eqP eq_y0 | y_neq0]. *)
(*   rewrite eq_y0 mulr0 !BP_val0 ?mulr0 //; last by rewrite -eq_y0 rootqy. *)
(*   by have := rootrxy; rewrite eq_y0 mulr0. *)
(* have yvn0 : BP_val y q fT != 0. *)
(*   rewrite neqr_lt -(rmorph0 _ : ratr 0 = 0) ?BP_lt_inf ?BP_lt_sup //. *)
(*   by rewrite !rmorph0 -neqr_lt. *)
(* apply/(divIf yvn0)/esym; rewrite (mulfK yvn0) -[x in LHS](mulfK y_neq0). *)
(* move: q qn0 rootqy yvn0 => q' q'n0 rootq'y yvn0. *)
(* wlog: q' q'n0 rootq'y yvn0 / q'.[0] != 0. *)
(*   move=> H; pose s := gdcop 'X q'. *)
(*   have sn0 : s != 0 by rewrite /s cauchyreals.gdcop_eq0 negb_and q'n0. *)
(*   have rootsy : root (map_poly ratr s) y. *)
(*     by rewrite gdcop_map /= root_gdco ?map_poly_eq0 // rootq'y map_polyX rootX. *)
(*   have yvsn0 : BP_val y s fT != 0. *)
(*     rewrite neqr_lt -(rmorph0 _ : ratr 0 = 0) ?BP_lt_inf ?BP_lt_sup //. *)
(*     by rewrite !rmorph0 -neqr_lt. *)
(*   have nroots0 : s.[0] != 0. *)
(*     by rewrite -rootE root_gdco ?q'n0 // rootX eq_refl /= andbF. *)
(*   have -> := H s sn0 rootsy yvsn0 nroots0; congr (_ / _); apply/eqP. *)
(*   rewrite BP_val_eq // ?BP_lt_inf ?BP_lt_sup // ?BP_lt_ax ?BP_lt_xb //=. *)
(*   by apply/(BP_val_root q'n0 rootq'y)/BP_rootx. *)
(* move=> q'0n0; pose P := polyXY.div_annihilant r q'. *)
(* have Pn0 : P != 0 by apply: polyXY.div_annihilant_neq0. *)
(* have rootPxy : root (map_poly ratr P) ((x * y) / y). *)
(*   by apply/rootP/polyXY.map_div_annihilantP => //; apply/rootP. *)
(* have rootpxy : root (map_poly ratr p) ((x * y) / y). *)
(*   by rewrite mulfK ?rootpx ?y_neq0. *)
(* apply/eqP; apply/ (BP_valpP _ pn0 rootpxy Pn0 rootPxy) => //; split; last first. *)
(*   by apply/rootP/polyXY.map_div_annihilantP => //=; apply/rootP/BP_val_root. *)
(* move: x rootrxy => x'; move: y y_neq0 rootq'y => y' y'_neq0 rootq'y rootrxy. *)
(* set xb := BP_val _ _ _; set yb := BP_val _ _ _. *)
(* have BP_gt_0 z Q (Qn0 : Q != 0) (rootQz : root (map_poly ratr Q) z) : *)
(*                    (z > 0) = ((BP_val z Q fT) > 0).  *)
(*   by rewrite -(rmorph0 _ : ratr 0 = 0 :> fT) BP_lt_inf ?rmorph0. *)
(* have BP_lt_0 z Q (Qn0 : Q != 0) (rootQz : root (map_poly ratr Q) z) : *)
(*                    (z < 0) = ((BP_val z Q fT) < 0).  *)
(*   by rewrite -(rmorph0 _ : ratr 0 = 0 :> fT) BP_lt_sup ?rmorph0. *)
(* suff Hnorm1 : forall qa qb : rat, 0 <= qa -> ratr qa < `|x' * y' / y'| < ratr qb -> *)
(*     ratr qa < `| xb / yb|  < ratr qb. *)
(*   move=> qa qb /andP[lt_qaxy lt_xyqb]. *)
(*   case: (ltrgtP (x' * y' / y' ) 0) => [lt_x'y'0| lt_0x'y'| eq_x'y'0]. *)
(*   + have -> : xb / yb = - `| xb / yb |. *)
(*       rewrite ltr0_norm ?opprK //. *)
(*       have := y'_neq0; rewrite neqr_lt => /orP[lt_y'0 | lt_0y']. *)
(*         rewrite ltr_ndivr_mulr ?mul0r -?BP_gt_0 -?BP_lt_0 //. *)
(*         by have := lt_x'y'0; rewrite (ltr_ndivr_mulr _ _ lt_y'0) mul0r. *)
(*       rewrite ltr_pdivr_mulr ?mul0r -?BP_gt_0 -?BP_lt_0 //. *)
(*       by have := lt_x'y'0; rewrite (ltr_pdivr_mulr _ _ lt_0y') mul0r. *)
(*     rewrite ltr_oppr ltr_oppl andbC -!rmorphN /=. *)
(*     suff : ratr (Num.max (-qb) 0) < `|xb / yb| < ratr (-qa).  *)
(*       move=> /andP[]; move/(ler_lt_trans _) => ->; rewrite ?andTb // ler_rat. *)
(*       by rewrite ler_maxr lerr. *)
(*     apply: Hnorm1; first by rewrite ler_maxr lerr orbT. *)
(*     rewrite (ltr0_norm lt_x'y'0) rmorphN lter_oppE /= lt_qaxy andbT ltr_oppr. *)
(*     case: maxrP => _; first by rewrite rmorphN opprK /= lt_xyqb. *)
(*     by rewrite rmorph0 oppr0 lt_x'y'0.  *)
(*   + have -> : xb / yb = `| xb / yb |. *)
(*       rewrite gtr0_norm //. *)
(*       have := y'_neq0; rewrite neqr_lt => /orP[lt_y'0 | lt_0y']. *)
(*         rewrite ltr_ndivl_mulr ?mul0r -?BP_gt_0 -?BP_lt_0 //. *)
(*         by have := lt_0x'y'; rewrite (ltr_ndivl_mulr _ _ lt_y'0) mul0r. *)
(*       rewrite ltr_pdivl_mulr ?mul0r -?BP_gt_0 -?BP_lt_0 //. *)
(*       by have := lt_0x'y'; rewrite (ltr_pdivl_mulr _ _ lt_0y') mul0r. *)
(*     suff : ratr (Num.max qa 0) < `|xb / yb | < ratr qb. *)
(*       move=> /andP[]; move/(ler_lt_trans _) => ->; rewrite ?andTb // ler_rat. *)
(*       by rewrite ler_maxr lerr. *)
(*     apply/Hnorm1; first by rewrite ler_maxr lerr orbT. *)
(*     rewrite (gtr0_norm lt_0x'y'); case: maxrP => _; first by rewrite /= lt_qaxy. *)
(*     by rewrite rmorph0 lt_0x'y' lt_xyqb. *)
(*   have /eqP eq_x'0 : x' == 0. *)
(*     by have /eqP := eq_x'y'0; rewrite !mulf_eq0 invr_eq0 (negbTE y'_neq0) !orbF. *)
(*   rewrite /xb eq_x'0 mul0r BP_val0 // ?mul0r ?ltr0q ?ltrq0. *)
(*     have := lt_qaxy; have := lt_xyqb. *)
(*     by rewrite eq_x'0 !mul0r ltr0q ltrq0 => -> ->. *)
(*   by have := rootrxy; rewrite eq_x'0 mul0r. *)
(* move=> qa; wlog: qa / 0 < qa => [ihp qb| lt_0a]. *)
(*   rewrite ler_eqVlt => /orP[/eqP/esym ->| lt_0qa]; last first. *)
(*     by apply: ihp => //; apply/ltrW. *)
(*   rewrite !rmorph0 => /andP[lt_0n lt_nb]. *)
(*   have [qa' /andP[lt_0a' lt_a'n]] := rat_dense lt_0n. *)
(*   suff: ratr qa' < `|xb / yb| < ratr qb. *)
(*     move=> /andP[lt_q'n ->]; rewrite andbT. *)
(*     by apply/(ltr_trans _ lt_q'n); have := lt_0a'; rewrite !ltr0q. *)
(*   apply/ihp; rewrite ?lt_a'n ?lt_nb //; have := lt_0a'; rewrite ltr0q //. *)
(*   by apply/ltrW. *)
(* have BP_infn z Q (Qn0 : Q != 0) (rootQ : root (map_poly ratr Q) z) u : *)
(*   (ratr u < `|z|) = (ratr u < `|BP_val z Q fT|). *)
(*   case: ltrgt0P; last by move=> Heq; rewrite Heq BP_val0 ?normr0 ?ltrq0 // -Heq. *)
(*     by rewrite (BP_gt_0 _ _ Qn0 rootQ) => /gtr0_norm ->; rewrite BP_lt_inf. *)
(*   rewrite (BP_lt_0 _ _ Qn0 rootQ) => /ltr0_norm ->. *)
(*   by rewrite ltr_oppr -rmorphN BP_lt_sup ?rmorphN //= ltr_oppr. *)
(* have BP_supn z Q (Qn0 : Q != 0) (rootQ : root (map_poly ratr Q) z) u : *)
(*   (`|z| < ratr u) = (`|BP_val z Q fT| < ratr u). *)
(*   case: ltrgt0P; last by move=> Heq; rewrite Heq BP_val0 ?normr0 ?ltr0q // -Heq. *)
(*     by rewrite (BP_gt_0 _ _ Qn0 rootQ) => /gtr0_norm ->; rewrite BP_lt_sup. *)
(*   rewrite (BP_lt_0 _ _ Qn0 rootQ) => /ltr0_norm ->. *)
(*   by rewrite ltr_oppl -rmorphN BP_lt_inf ?rmorphN //= ltr_oppl. *)
(* move=> qb _ {BP_gt_0 BP_lt_0 yvn0 q'0n0 P Pn0 rootPxy rootpxy}. *)
(* rewrite normrM [`|xb / yb|]normrM !normfV => /andP[lt_axy lt_xyb]. *)
(* have lt_0y: 0 < `|y'| by rewrite normr_gt0. *)
(* have lt_0xy: 0 < `|x' * y'|/`|y'| by apply/(ltr_trans _ lt_axy); rewrite ltr0q. *)
(* have lt_0x : 0 < `|x' * y'|. *)
(*   by have := lt_0xy; rewrite ltr_pdivl_mulr // mul0r. *)
(* have lt_0b : 0 < qb by have := (ltr_trans lt_0xy lt_xyb); rewrite ltr0q. *)
(* pose e := Num.min ((`|x' * y'| / `|y'| ) / ratr qa) (ratr qb / (`|x' * y'| / `|y'|)). *)
(* have e_gt0 : 0 < e. *)
(*   rewrite ltr_minr ltr_pdivl_mulr ?ltr0q // ?mul0r ?mul1r. *)
(*   by rewrite lt_0xy /= ltr_pdivl_mulr // mul0r ltr0q lt_0b. *)
(* have e_gt1 : Num.sqrt e > 1. *)
(*   rewrite -sqrtr1 ltr_sqrt // ltr_minr ltr_pdivl_mulr ?ltr0q // mul1r. *)
(*   by rewrite lt_axy /= ltr_pdivl_mulr // mul1r lt_xyb. *)
(* have [qe /andP[lt_1qe lte]] := rat_dense e_gt1. *)
(* have lt_0qe : 0 < qe by have := (ltr_trans ltr01 lt_1qe); rewrite ltr0q. *)
(* have lt_qee : ratr qe * ratr qe < e. *)
(*   by rewrite -(sqr_sqrtr (ltrW e_gt0)) expr2 ltr_pmul // ?ler0q ltrW. *)
(* have := lt_1qe; rewrite -(ltr_pmulr _ lt_0x). *)
(* move/rat_dense => [qx /andP[lt_xqx lt_qxxe]]. *)
(* have := lt_1qe; rewrite -(ltr_pmulr _ lt_0y). *)
(* move/rat_dense => [qy /andP[lt_yqy lt_qyye]]. *)
(* have Hqinf : ratr qa < ratr (qx / qy / qe) :> fT. *)
(*   suff : ratr qa < ratr (qx / qy / qe) :> T by rewrite !ltr_rat. *)
(*   apply/(@ltr_trans _ (`|x' * y'|/`|y'|/(ratr qe * ratr qe))). *)
(*     rewrite ltr_pdivl_mulr; last by rewrite mulr_gt0 ?ltr0q ?lt_0qe. *)
(*     rewrite mulrC -ltr_pdivl_mulr ?ltr0q //; apply/(ltr_le_trans lt_qee). *)
(*     by rewrite ler_minl lerr. *)
(*   rewrite ltr_pdivr_mulr; last by rewrite mulr_gt0 ?ltr0q. *)
(*   rewrite !rmorphM mulrA !fmorphV /= [X in _ < X * _]divfK; last first. *)
(*     by rewrite (gtr_eqF) ?ltr0q ?lt_0qe. *)
(*   have -> : ratr qx / ratr qy * ratr qe = ratr qx / (ratr qy / ratr qe) :> T. *)
(*     by rewrite -mulrA; congr(_ * _); rewrite [RHS]invfM invrK. *)
(*   apply/ltr_pmul; rewrite ?invr_ge0 ?normr_ge0 // ltf_pinv //=. *)
(*     by rewrite ltr_pdivr_mulr ?ltr0q. *)
(*   apply: divr_gt0; first by apply/(ltr_trans lt_0y lt_yqy). *)
(*   by rewrite ltr0q lt_0qe. *)
(* have Hqsup : ratr (qx * qe / qy) < ratr qb :> fT. *)
(*   suff : ratr (qx * qe / qy) < ratr qb :> T.  *)
(*     by rewrite ltr_rat [in X in _ -> X]ltr_rat. *)
(*   apply/(@ltr_trans _ (`|x' * y'|/`|y'| * (ratr qe * ratr qe))); last first. *)
(*     rewrite -ltr_pdivl_mull //; apply/(ltr_le_trans lt_qee); rewrite mulrC. *)
(*     by rewrite ler_minl lerr orbT. *)
(*   rewrite mulrA -ltr_pdivr_mulr ?ltr0q // [X in _ < X]mulrAC. *)
(*   rewrite !rmorphM /= [X in X * _]mulrAC mulfK ?fmorphV /=; last first. *)
(*     by rewrite (gtr_eqF) ?ltr0q ?lt_0qe. *)
(*   apply/ltr_pmul; rewrite ?invr_ge0 // ?ltf_pinv //=. *)
(*   + by apply/ltrW/(ltr_trans lt_0x lt_xqx). *)
(*   + by apply/ltrW/(ltr_trans lt_0y lt_yqy). *)
(*   by apply/(ltr_trans lt_0y lt_yqy). *)
(* have H : 0 < `|yb| by rewrite -(rmorph0 _: ratr 0 = 0 :> fT) -BP_infn ?rmorph0. *)
(* rewrite (ltr_trans Hqinf) ?(ltr_trans _ Hqsup) //. *)
(*   have -> : qx * qe / qy = qx / (qy / qe) by rewrite invfM invrK mulrAC mulrA. *)
(*   rewrite rmorphM fmorphV /=; apply/ltr_pmul; rewrite ?invr_ge0 ?normr_ge0 //. *)
(*     by rewrite -BP_supn. *)
(*   rewrite ltf_pinv -?BP_infn //; last first. *)
(*     rewrite posrE ltr0q divr_gt0 //. *)
(*     by have := (ltr_trans lt_0y lt_yqy); rewrite ltr0q. *)
(*   by rewrite rmorphM fmorphV /= ltr_pdivr_mulr ?ltr0q. *)
(* rewrite mulrAC rmorphM fmorphV /=; apply/ltr_pmul; rewrite ?invr_ge0 //. *)
(* + apply/ltrW; rewrite ltr0q mulr_gt0 ?invr_gt0 //. *)
(*   by have := (ltr_trans lt_0x lt_xqx); rewrite ltr0q. *)
(* + by have := ltrW (ltr_trans lt_0y lt_yqy); rewrite !ler0q. *)
(* + by rewrite -BP_infn // rmorphM fmorphV /= ltr_pdivr_mulr ?ltr0q. *)
(* rewrite ltf_pinv //= -?BP_supn //. *)
(* by have := (ltr_trans lt_0y lt_yqy); rewrite posrE !ltr0q. *)
(* Qed. *)

(* Lemma BP_val_mono : *)
(*   (BP_val x p fT < BP_val y q fT) = (x < y). *)
(* Proof. *)
(* case: (ltrgtP x y) => [lt_yx | lt_xy | eq_xy]; last first. *)
(* + suff -> : BP_val x p fT = BP_val x q fT by rewrite eq_xy ltrr. *)
(*   apply/eqP; rewrite BP_val_eq -?BP_root ?BP_lt_inf ?BP_lt_sup // ?eq_xy //. *)
(*   by rewrite BP_val_root // -?eq_xy // BP_lt_ax ?BP_lt_xb. *)
(* + have /rat_dense [a /andP[]] := lt_xy. *)
(*   rewrite -(BP_lt_inf fT pn0 rootpx) -(BP_lt_sup fT qn0 rootqy). *)
(*   by move/ltr_trans => H; move/H/ltrW => H1; apply/negP/negP; rewrite -lerNgt. *)
(* have /rat_dense [a /andP[]] := lt_yx. *)
(* rewrite -(BP_lt_sup fT pn0 rootpx) -(BP_lt_inf fT qn0 rootqy). *)
(* by apply: ltr_trans. *)
(* Qed. *)

(* Lemma BP_val_mono_le : *)
(*   (BP_val y q fT <= BP_val x p fT) = (y <= x). *)
(* Proof. by rewrite !lerNgt BP_val_mono. Qed. *)

(* End BP_morph. *)

(* End BetterParams. *)

(* Variable R : rcfType. *)

(* Lemma root_annul_realalg_ratr (x : realalg) : *)
(*   root (map_poly ratr (annul_realalg x)) x. *)
(* Proof. *)
(* by have := (root_annul_realalg x); rewrite (eq_map_poly (fmorph_eq_rat _)). *)
(* Qed. *)

(* Definition from_RA (x : realalg) := *)
(*   BP_val x (annul_realalg x) R. *)

(* Lemma minCpoly_neq0_rat (x : {normT algC}) : *)
(*   sval (minCpolyP (nval x)) != 0. *)
(* Proof. by have [[_ /monic_neq0]] := svalP (minCpolyP (nval x)). Qed. *)

(* Lemma root_minCpoly_rat_norm (x : {normT algC}) : *)
(*   root (map_poly ratr (sval (minCpolyP (nval x)))) x. *)
(* Proof.  *)
(* set u := @nval _; have [[H _ _]]:= svalP (minCpolyP (nval x)); move: H. *)
(* have /eq_map_poly <- : u \o ratr =1 ratr by apply/fmorph_eq_rat. *)
(* move=> H; have := (root_minCpoly (nval x)); rewrite {1}H map_poly_comp. *)
(* by rewrite !rootE /= horner_map /=. *)
(* Qed. *)

(* Lemma from_RA_is_rmorphism : rmorphism from_RA. *)
(* Proof. *)
(* split. *)
(*   move=> x y; rewrite /from_RA.  *)
(*   by apply: BP_valB; rewrite ?root_annul_realalg_ratr ?annul_realalg_neq0. *)
(* split; last first. *)
(*   by rewrite /from_RA BP_val1 ?root_annul_realalg_ratr ?annul_realalg_neq0. *)
(* move=> x y; rewrite /from_RA. *)
(* by apply: BP_valM; rewrite ?root_annul_realalg_ratr ?annul_realalg_neq0. *)
(* Qed. *)

(* Canonical from_RA_rmorphism := RMorphism from_RA_is_rmorphism. *)

(* Definition from_aCR (x : {normT algC}) := *)
(*   BP_val x (sval (minCpolyP (nval x))) R. *)

(* Lemma from_aCR_is_rmorphism : rmorphism from_aCR. *)
(* split. *)
(*   move=> x y; rewrite /from_aCR.  *)
(*   by apply: BP_valB; rewrite ?minCpoly_neq0_rat ?root_minCpoly_rat_norm. *)
(* split; last first. *)
(*   by rewrite /from_aCR BP_val1 ?minCpoly_neq0_rat ?root_minCpoly_rat_norm. *)
(* move=> x y; rewrite /from_aCR. *)
(* by apply: BP_valM; rewrite ?minCpoly_neq0_rat ?root_minCpoly_rat_norm. *)
(* Qed. *)

(* Canonical from_aCR_rmorphism := RMorphism from_aCR_is_rmorphism. *)
*)
End AlgrNormT. 
(*
(* Arguments from_RA [R]. *)
(* Arguments from_aCR [R]. *)

(* Section AlgrAlgC. *)

(* Variable T : numClosedFieldType. *)

(* Definition algr (x : algC) : T := *)
(*   let x_re := NormT (algCreal_Re x) in *)
(*   let x_im := NormT (algCreal_Im x) in *)
(*   (nval (from_aCR x_re)) + 'i * (nval (from_aCR x_im)). *)

(* (* :TODO: comprendre le bug *) *)

(* (* Lemma algr_planteR x y : *) *)
(* (*  NormT (algCreal_Re (x - y)) = NormT (algCreal_Re x) - NormT (algCreal_Re y). *) *)
(* (* Proof. *) *)
(* (* by apply/nval_inj; rewrite /= raddfB. *) *)
(* (* Qed. *) *)
(* (* Lemma algr_planteI x y : *) *)
(* (*  NormT (algCreal_Im (x - y)) = NormT (algCreal_Im x) - NormT (algCreal_Im y). *) *)
(* (* Proof. *) *)
(* (* by apply/nval_inj; rewrite /= raddfB. *) *)
(* (* Qed. *) *)

(* (* Lemma algr_is_additive2 : additive algr. *) *)
(* (* Proof. *) *)
(* (* move=> x y /=; rewrite /algr opprD addrACA -mulrBr -!rmorphB /=. *) *)
(* (* by rewrite algr_planteR algr_planteI. *) *)
(* (* Qed. *) *)

(* (* Lemma algr_is_additive3 : additive algr. *) *)
(* (* Proof. *) *)
(* (* move=> x y /=; rewrite /algr opprD addrACA -mulrBr -!rmorphB /=. *) *)
(* (* by congr (nval (_ _) + 'i * nval (from_aCR _)); rewrite ?algr_planteR ?algr_planteI. *) *)
(* (* Qed. *) *)

(* (* Lemma algr_is_additive : additive algr. *) *)
(* (* Proof. *) *)
(* (*   move=> x y /=; rewrite /algr opprD addrACA -mulrBr -!rmorphB /=. *) *)
(* (*   by congr (_ (_ _) +'i * nval (from_aCR _)); apply/nval_inj; rewrite /= raddfB. *) *)
(* (* Qed. *) *)

(* Lemma algr_is_rmorphism : rmorphism algr. *)
(* Proof. *)
(* split. *)
(*   move=> x y /=; rewrite /algr opprD addrACA -mulrBr -!rmorphB /=. *)
(*   by congr (_ + (_ * _)); congr (nval (_ _)); apply/nval_inj; rewrite /= raddfB. *)
(* split; rewrite /algr; last first. *)
(* + have -> : NormT (algCreal_Re 1) = 1 by apply/nval_inj/Creal_ReP/Creal1. *)
(*   have -> : NormT (algCreal_Im 1) = 0 by apply/nval_inj/Creal_ImP/Creal1. *)
(*   by rewrite rmorph0 rmorph1 mulr0 addr0. *)
(* move=> x y /=; rewrite /algr mulC_rect -!rmorphM -!rmorphB -!rmorphD /=. *)
(* congr (_ + (_ * _)); congr (nval (_ _)); apply/nval_inj; *)
(* rewrite /= {1}(Crect x) {1}(Crect y) mulC_rect. *)
(*   by apply/Re_rect; rewrite ?realB ?realD // realM ?Creal_Im ?Creal_Re. *)
(* by apply/Im_rect; rewrite ?realB ?realD // realM ?Creal_Im ?Creal_Re. *)
(* Qed. *)

(* Canonical algr_rmorphism := RMorphism algr_is_rmorphism. *)
(* (* Canonical algr_additive := [additive of algr_rmorphism]. *) *)

(* Lemma algr_mono : {mono algr : x y / lec x y >-> lec x y}. *)
(* Proof. *)
(* move=> x y; rewrite /lec /algr /from_aCR !Re_rect ?Im_rect; *)
(*   do ? by apply: (@num_real (normT_realDomainType T)). *)
(* have H (R : numClosedFieldType) (a b : {normT R}) :  *)
(*   (a <= b) = (nval a <= nval b) by []. *)
(* rewrite ltr_neqAle eqr_le -!H. *)
(* rewrite !BP_val_mono_le ?root_minCpoly_rat_norm ?minCpoly_neq0_rat //=. *)
(* by rewrite !H /= -eqr_le -ltr_neqAle. *)
(* Qed. *)

(* Lemma Croots_algr P :  *)
(*   map algr (Croots (map_poly ratr P)) = Croots (map_poly ratr P). *)
(* Proof. *)
(* case: (boolP (P == 0)) => [/eqP ->| P_n0]; first by rewrite !map_poly0 !Croots0. *)
(* apply: (eq_sorted (@lec_trans _) (@lec_asym _) _ (@Croots_sorted _ _)). *)
(*   move H : (Croots _) => s. *)
(*   have {H} : sorted lec s by rewrite -H Croots_sorted. *)
(*   elim: s => // x s ihs /= H; have /path_sorted/ihs Hs := H.  *)
(*   rewrite path_min_sorted // => y /mapP [z z_in ->]; rewrite algr_mono. *)
(*   by have /order_path_min := H; move/(_ (@lec_trans _))/allP; apply. *)
(* wlog: P P_n0 / separable_poly P; last first. *)
(*   move=> P_seq; apply: uniq_perm_eq. *)
(*   + rewrite map_inj_uniq; last by apply: fmorph_inj. *)
(*     by apply: Croots_separable; rewrite separable_map. *)
(*   + by apply: Croots_separable; rewrite separable_map. *)
(*   move=> x; apply/mapP/idP. *)


(*   move=> x; apply/mapP/CrootsP; first by rewrite map_poly_eq0. *)
(*   + move=> [y /CrootsP y_in ->]. *)
(*     have /eq_map_poly <- : algr \o ratr =1 ratr by apply: fmorph_eq_rat. *)
(*     by rewrite map_poly_comp_id0 ?rmorph0 // fmorph_root y_in // map_poly_eq0. *)
(*   move=> root_P; have x_in : x \in Croots (map_poly ratr P). *)
(*     by apply/CrootsP/root_P; rewrite map_poly_eq0. *)
(*   pose i := index x (Croots (map_poly ratr P)). *)
(*   pose y := (nth (0 : algC) (Croots (map_poly ratr P)) i). *)
(*   have y_in : y \in Croots (map_poly ratr P). *)
(*     apply/mem_nth; have := x_in; rewrite -index_mem !Croots_size !map_poly_eq0. *)
(*     by rewrite (negbTE P_n0) !size_map_poly. *)
(*   exists y => //. *)

(* Search _ (_ =1 _) injective. *)
(* Search _ index. *)
(* Search _ ratr (_ =1 _). *)
(* eq_map_poly: forall (aR rR : ringType) (f g : aR -> rR), f =1 g -> map_poly f =1 map_poly g *)
(* fmorph_eq_rat: forall (rR : unitRingType) (f : {rmorphism rat -> rR}), f =1 ratr *)
(* fmorph_rat: *)
(*   forall (aR : fieldType) (rR : unitRingType) (f : {rmorphism aR -> rR}) (a : rat), *)
(*   f (ratr a) = ratr a *)

(* Search _ separable_poly map_poly. *)
(* have /Croots_separable :  *)
(* Search _ perm_eq flatten. *)

(* (* Décomposition d'un poly rationnel en facteurs irréductibles *) *)

(* apply: uniq_perm_eq; last first. *)
(* move=> x /=. *)
(* apply/mapP/CrootsP. *)

(* Search _ perm_eq. *)
(* uniq_perm_eq: forall (T : eqType) (s1 s2 : seq T), uniq s1 -> uniq s2 -> s1 =i s2 -> perm_eq s1 s2 *)
(* Search _ path. *)
(* About eq_sorted. *)
(* order_path_min: *)
(*   forall (T : eqType) (leT : rel T), *)
(*   transitive leT -> forall (x : T) (s : seq T), path leT x s -> all (leT x) s *)


(* Lemma algr_inv_subproof (x : T) : *)
(*   algebraicOver ratr x -> {y : algC | algr y = x}. *)
(* Proof. *)
(* move=> x_alg. *)

(* End AlgrAlgC. *)

(* Section AlgrComplexalg. *)

(* Variable T : numClosedFieldType. *)

(* Definition algrCA (x : complexalg) : T := *)
(*   (nval (from_RA (complex.Re x))) + 'i * (nval (from_RA (complex.Im x))). *)

(* Lemma algrCA_is_rmorphism : rmorphism algrCA. *)
(* Proof. *)
(* split. *)
(* + move=> [xr xi] [yr yi]; rewrite /algrCA /= !rmorphB /= mulrBr opprD !addrA. *)
(*   by congr (_ + _); rewrite addrAC. *)
(* split; last by rewrite /algrCA /= rmorph0 rmorph1 mulr0 addr0. *)
(* move=> [xr xi] [yr yi]; rewrite /algrCA /= rmorphB !rmorphD !rmorphM !mulrDr /=. *)
(* rewrite !mulrDl ![_ * ('i * _)]mulrCA addrAC [X in (_ + X + _)]addrC !addrA. *)
(* by rewrite !mulrA; congr (_ + _ + _ + _); rewrite -expr2 sqrCi -mulrA mulN1r. *)
(* Qed. *)

(* Canonical algrCA_rmorphism := RMorphism algrCA_is_rmorphism. *)

(* End AlgrComplexalg. *)

*)

End Algr. 


End Archi.

Export Archi.ArchiNumDomain.Exports Archi.ArchiNumField.Exports.
Export Archi.ArchiNumClosedField.Exports Archi.ArchiRealDomain.Exports.
Export Archi.ArchiRealField.Exports Archi.ArchiRealClosedField.Exports.



(* minimal polynomial of an algebraic number of a numClosedField *)

(* Variable x : R. *)
(* Hypothesis x_alg : algebraicOver ratr x. *)