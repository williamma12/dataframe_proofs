Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Lists.List.

From DF Require Import Dataframe.

(* Define terms. *)
Inductive data_term : Type :=
| DEmpty : data_term
| DString : data_term             
| DNat : data_term
| CastDType :
    (** New type **) data_term ->
    (** Original term **) data_term ->
    data_term              
| Mask :
    (** Bool to keep or make empty **) bool ->
    (** Original term **) data_term ->
    data_term
| Filter :
    (** Function to go determine if keep **) data_term -> bool ->
    (** Original term **) data_term ->
    data_term
| Map :
    (** Mapping function **) data_term -> data_term ->
    (** Original term **) data_term ->
    data_term
| Update :
    (** New term to be **) data_term ->
    (** Original term **) data_term ->
    data_term.
(* 
   Update captures Transpose, ToLabels, FromLabels, Concat, and InferDTypes
   as those functions at the individual data cell level essentially
   gets a new data value to replace the old one with.
*)

Inductive dvalue : data_term -> Prop :=
| dv_empty : dvalue DEmpty
| dv_nat : dvalue DNat
| dv_string : dvalue DString.

Hint Constructors dvalue : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : data_term -> data_term -> Prop :=
| ST_CastEmpty : forall d,
    CastDType d DEmpty --> d
| ST_CastToString : forall d,
    CastDType DString d --> DString
| ST_CastNatToNat :
    CastDType DNat DNat --> DNat
| ST_MaskFalse : forall d,
    Mask false d --> DEmpty
| ST_MaskTrue : forall d,
    Mask true d --> d
| ST_FilterTrue : forall d__in d d',
    CastDType d__in d --> d' ->
    Filter d__in true d' --> d'
| ST_FilterFalse : forall d__in d d',
    CastDType d__in d --> d' ->
    Filter d__in false d' --> DEmpty
| ST_Map : forall d__in d__out d d',
    CastDType d__in d --> d' ->
    Map d__in d__out d' --> d__out
| ST_Update : forall d__new d__old,
    Update d__new d__old --> d__new
        
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Inductive dtype : Type :=
| Empty : dtype
| String : dtype
| Nat : dtype.

(* Define the data typing for operations. *)
Reserved Notation "'⊢' t '∈' T" (at level 40).

Inductive has_type : data_term -> dtype -> Prop :=
| T_Empty :
    ⊢ DEmpty ∈ Empty
| T_String :
    ⊢ DString ∈ String
| T_Nat :
    ⊢ DNat ∈ Nat
| T_CastEmpty : forall d D,
    ⊢ d ∈ D ->
    ⊢ CastDType d DEmpty ∈ D
| T_CastToString : forall d D,
    ⊢ d ∈ D ->
    ⊢ CastDType DString d ∈ String
| T_CastNatToNat :
    ⊢ CastDType DNat DNat ∈ Nat
| T_MaskFalse : forall d D,
    ⊢ d ∈ D ->
    ⊢ Mask false d ∈ Empty
| T_MaskTrue : forall d D,
    ⊢ d ∈ D ->
    ⊢ Mask true d ∈ D
| T_FilterTrue : forall d__in d d' D D__in,
    ⊢ d ∈ D ->
    ⊢ d__in ∈ D__in ->
    CastDType d__in d --> d' ->
    ⊢ d' ∈ D__in ->
    ⊢ Filter d__in true d' ∈ D__in
| T_FilterFalse : forall d__in d d' D D__in,
    ⊢ d ∈ D ->
    ⊢ d__in ∈ D__in ->
    CastDType d__in d --> d' ->
    ⊢ d' ∈ D__in ->
    ⊢ Filter d__in false d' ∈ Empty
| T_Map : forall d__in d__out d d' D D__in D__out,
    ⊢ d ∈ D ->
    ⊢ d__in ∈ D__in ->
    ⊢ d__out ∈ D__out ->
    CastDType d__in d --> d' ->
    ⊢ d' ∈ D__in ->
    ⊢ Map d__in d__out d' ∈ D__out
| T_Update : forall d__new d__old D,
    ⊢ d__new ∈ D ->
    ⊢ Update d__new d__old ∈ D

where "'⊢' t '∈' T" := (has_type t T).

Hint Constructors has_type : core.

Theorem progress : forall t T,
    ⊢ t ∈ T ->
    dvalue t \/ (exists t', t --> t').
Proof.
  intros t T H.
  induction H; auto; right; try (destruct IHhas_type; eauto).
  - exists DNat.
    apply ST_CastNatToNat.
  - exists d'.
    eapply ST_FilterTrue.
    apply H1.
  - exists DEmpty.
    eapply ST_FilterFalse.
    apply H1.
  - exists d__out.
    eapply ST_Map.
    apply H2.
Qed.

Theorem preservation: forall t t' T,
    ⊢ t ∈ T ->
    t --> t' ->
    ⊢ t' ∈ T.
Proof.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT; intros t' HE; try (inversion HE; subst); eauto.
Qed.
