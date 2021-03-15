Set Warnings "-notation-overridden,-parsing".
From DF Require Import Dataframe.

(* Define terms. *)
Inductive op : Type :=
| DataFrame :
    (** Row index position and label **) list Dataframe.Index ->
    (** Row data types **) list Dataframe.dtype ->
    (** Column index position and label **) list Dataframe.Index ->
    (** Column data types **) list Dataframe.dtype ->
    (** Actual values **) list (list Dataframe.data_value) -> op
| Transpose : op -> op
| Mask :
    (** Mask positions. **) list nat ->
    (** Axis to apply mask over **) Dataframe.Axis ->
    op -> op
| Filter :
    (** Filter function **) (list Dataframe.data_value -> bool) ->
    (** Axis to filter over **) Dataframe.Axis ->
    op -> op
| ToLabels :
    (** Index to use as index labels **) nat ->
    (** Axis to update the index for. **) Dataframe.Axis ->
    op -> op
| FromLabels :
    (** Axis to take the index from. **) Dataframe.Axis ->
    op -> op
| Map :
    (** Mapping function **) (list Dataframe.data_value -> list Dataframe.data_value) ->
    (** Possible dtypes each index **) list (list Dataframe.dtype) ->
    (** Axis to map over. **) Dataframe.Axis ->
    op -> op
| Concat :
    (** How to concat **) Dataframe.Set_Combine ->
    (** Axis to concat along. **) Dataframe.Axis ->    
    (** Other dataframe to concat **) op ->
    (** Self **) op ->
    op
| InferDTypes :
    (** Axis to infer dtypes for. **) Dataframe.Axis ->
    op -> op.

Inductive dfvalue : op -> Prop :=
| df_DataFrame : forall row__index row__dtypes col__index col__dtypes values,
    dfvalue (DataFrame row__index row__dtypes col__index col__dtypes values).

Hint Constructors dfvalue : Dataframes.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : op -> op -> Prop :=
| ST_Transpose : forall df,
    df --> Transpose df
| ST_Mask : forall mask_positions axis df,
    df --> Mask mask_positions axis df
| ST_Filter : forall filter_func axis df,
    df --> Filter filter_func axis df
| ST_ToLabels : forall index_ind axis df,
    df --> ToLabels index_ind axis df
| ST_FromLabels : forall axis df,
    df --> FromLabels axis df
| ST_Map : forall map_func map_dtype axis df,
    df --> Map map_func map_dtype axis df
| ST_Concat : forall concat_type axis other self,
    self --> Concat concat_type axis other self
| ST_InferDTypes : forall axis df,
    df -> InferDTypes axis df
    
  where "t '-->' t'" := (step t t').
(*
(* Define the data typing for operations. *)
Reserved Notation "'⊢' df '∈' rDT ',' cDT " (at level 40).

Inductive has_dtype : op -> list dtype -> list dtype -> Prop :=

where "'⊢' df '∈' rDT ',' cDT" := (has_dtype df rDT cDT).

Hint Constructors has_dtype : core.


Theorem progress : forall df rDT cDT,
    ⊢ df ∈ rDT, cDT ->
                dfvalue df \/ exists df', df --> df'.
Proof.
  intros df rDT cDT H.
  induction H; eauto; right.
  - (** ToLabels **)
    destruct axis0; eauto.
Qed.

Theorem preservation: forall df df' rDT cDT,
    ⊢ df ∈ rDT, cDT ->
    df --> df' ->
    exists rDT' cDT', ⊢ df' ∈ rDT', cDT'.
Proof.
  intros df df' rDT cDT HT HE.
  generalize dependent df'.
  induction HT; intros df' HE; try (inversion HE; subst); eauto.
Qed.
*)
