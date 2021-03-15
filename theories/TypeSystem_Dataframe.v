Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Lists.List.

From DF Require Import Dataframe.

(* Define terms. *)
Inductive op : Type :=
| DataFrame :
   Dataframe.DataFrame -> op
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

(*
Inductive dfvalue : op -> Prop :=
| dfvalue_DataFrame : dfvalue DataFrame.
 *)
Inductive dfvalue : op -> Prop :=
| df_DataFrame : forall df_obj,
    (*
    Datatypes.length row__index = Datatypes.length row__dtypes ->
    Datatypes.length col__index = Datatypes.length col__dtypes ->
    Dataframe.valid_matrix values = true ->
    Dataframe.matrix_length values = Datatypes.length row__index ->
    Dataframe.matrix_width values = Datatypes.length col__index ->
    Dataframe.dtype_eqb_lsts (map infer_dtypes values) row__dtypes = true ->
    Dataframe.dtype_eqb_lsts (map infer_dtypes (Dataframe.transpose_matrix values)) col__dtypes = true ->
    Dataframe.valid_index row__index = true ->
    Dataframe.valid_index col__index = true ->
    dfvalue (DataFrame row__index row__dtypes col__index col__dtypes values).
     *)
    Dataframe.DataFrame -> dfvalue (DataFrame df_obj).

Hint Constructors dfvalue : core.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : op -> op -> Prop :=
| ST_TransposeValue : forall df df_obj,
    dfvalue df ->
    df = DataFrame df_obj ->
    Transpose df --> DataFrame (Dataframe.Transpose df_obj)
| ST_TransposeStep : forall df df',
    df --> df' ->
    Transpose df --> Transpose df'
| ST_TransposeTwice : forall df,
    dfvalue df ->
    Transpose (Transpose df) --> df
| ST_MaskValue : forall mask_position axis df df_obj,
    dfvalue df ->
    df = DataFrame df_obj ->
    Mask mask_position axis df --> DataFrame (Dataframe.Mask mask_position axis df_obj)
| ST_MaskStep : forall mask_position axis df df',
    df --> df' ->
    Mask mask_position axis df --> Mask mask_position axis df'
(*
| ST_FilterNone : forall axis df,
    dfvalue df ->
    Filter (fun row => true) axis df --> df
 *)
| ST_FilterValue : forall filter_func axis df df_obj,
    dfvalue df ->
    df = DataFrame df_obj ->
    Filter filter_func axis df --> DataFrame (Dataframe.Filter filter_func axis df_obj)
| ST_FilterStep : forall filter_func axis df df',
    df --> df' ->
    Filter filter_func axis df --> Filter filter_func axis df'
| ST_ToLabelsValue : forall index_ind axis df df_obj,
    dfvalue df ->
    df = DataFrame df_obj ->
    ToLabels index_ind axis df --> DataFrame (Dataframe.ToLabels index_ind axis df_obj)
| ST_ToLabelsStep : forall index_ind axis df df',
    df --> df' ->
    ToLabels index_ind axis df --> ToLabels index_ind axis df'
| ST_FromLabelsValue : forall axis df df_obj,
    dfvalue df ->
    df = DataFrame df_obj ->
    FromLabels axis df --> DataFrame (Dataframe.FromLabels axis df_obj)
| ST_FromLabelsStep : forall axis df df',
    df --> df' ->
    FromLabels axis df --> FromLabels axis df'
| ST_ToFromLabels : forall axis df,
    dfvalue df ->
    ToLabels 0 axis (FromLabels axis df) --> df
| ST_MapValues : forall map_func map_dtype axis df df_obj,
    dfvalue df ->
    df = DataFrame df_obj ->
    Map map_func map_dtype axis df --> DataFrame (Dataframe.Map map_func map_dtype axis df_obj)
| ST_MapStep : forall map_func map_dtype axis df df',
    df --> df' ->
    Map map_func map_dtype axis df --> Map map_func map_dtype axis df'
| ST_ConcatValue : forall concat_type axis other other_obj self self_obj,
    dfvalue self ->
    dfvalue other ->
    self = DataFrame self_obj ->
    other = DataFrame other_obj ->
    Concat concat_type axis other self --> DataFrame (Dataframe.Concat concat_type axis other_obj self_obj)
| ST_ConcatStep : forall concat_type axis other self df,
    dfvalue self ->
    dfvalue other ->
    Concat concat_type axis other self --> df
| ST_InferDTypesValue : forall axis df df_obj,
    dfvalue df ->
    df = DataFrame df_obj ->
    InferDTypes axis df --> DataFrame (Dataframe.InferDTypes axis df_obj)
| ST_InferDTypesStep : forall axis df df',
    df --> df' ->
    InferDTypes axis df --> InferDTypes axis df'
                     
where "t '-->' t'" := (step t t').

Hint Constructors step : core.

(* Define the data typing for operations. *)
Reserved Notation "'⊢' df '∈' rDT ',' cDT " (at level 40).

Inductive has_dtype : op -> list dtype -> list dtype -> Prop :=
  | DT_Constructor : forall df_obj,
      ⊢ (DataFrame df_obj) ∈ (get_row_dtypes df_obj), (get_col_dtypes df_obj)
  | DT_Transpose : forall df row__dtypes col__dtypes df_obj,
      ⊢ df ∈ row__dtypes, col__dtypes ->
      df = DataFrame df_obj ->
      ⊢ DataFrame (Dataframe.Transpose df_obj) ∈ col__dtypes, row__dtypes
  | DT_TransposeTwice : forall df row__dtypes col__dtypes df_obj,
      ⊢ df ∈ row__dtypes, col__dtypes ->
      df = DataFrame df_obj ->                  
      ⊢ DataFrame (Dataframe.Transpose (Dataframe.Transpose df_obj)) ∈ row__dtypes, col__dtypes
  | DT_Mask : forall mask_positions axis df row__dtypes col__dtypes df_obj df_obj',
      ⊢ df ∈ row__dtypes, col__dtypes ->
      df = DataFrame df_obj -> 
      df_obj' = Dataframe.Mask mask_positions axis df_obj ->
      ⊢ DataFrame df_obj' ∈ (get_row_dtypes df_obj'), (get_col_dtypes df_obj')
  | DT_Filter : forall filter_func axis df row__dtypes col__dtypes df_obj df_obj',
      ⊢ df ∈ row__dtypes, col__dtypes ->
      df = DataFrame df_obj -> 
      df_obj' = Dataframe.Filter filter_func axis df_obj ->
      ⊢ DataFrame df_obj' ∈ (get_row_dtypes df_obj'), (get_col_dtypes df_obj')
  | DT_ToLabels : forall label_ind axis df row__dtypes col__dtypes df_obj df_obj',
      ⊢ df ∈ row__dtypes, col__dtypes ->
      df = DataFrame df_obj -> 
      df_obj' = Dataframe.ToLabels label_ind axis df_obj ->
      ⊢ DataFrame df_obj' ∈ (get_row_dtypes df_obj'), (get_col_dtypes df_obj')
  | DT_FromLabels : forall axis df row__dtypes col__dtypes df_obj df_obj',
      ⊢ df ∈ row__dtypes, col__dtypes ->
      df = DataFrame df_obj -> 
      df_obj' = Dataframe.FromLabels axis df_obj ->
      ⊢ DataFrame df_obj' ∈ (get_row_dtypes df_obj'), (get_col_dtypes df_obj')
  | DT_Map : forall map_func map_dtypes axis df row__dtypes col__dtypes df_obj df_obj',
      ⊢ df ∈ row__dtypes, col__dtypes ->
      df = DataFrame df_obj -> 
      df_obj' = Dataframe.Map map_func map_dtypes axis df_obj ->
      ⊢ DataFrame df_obj' ∈ (get_row_dtypes df_obj'), (get_col_dtypes df_obj')
  | DT_Concat : forall concat_type axis other self other_row__dtypes other_col__dtypes self_row__dtypes self_col__dtypes other_obj self_obj df_obj',
      ⊢ self ∈ self_row__dtypes, self_col__dtypes ->
      ⊢ other ∈ other_row__dtypes, other_col__dtypes ->                               
      self = DataFrame self_obj ->
      other = DataFrame other_obj ->
      df_obj' = Dataframe.Concat concat_type axis other_obj self_obj ->
      ⊢ DataFrame df_obj' ∈ (get_row_dtypes df_obj'), (get_col_dtypes df_obj')
  | DT_InferDTypes : forall axis df row__dtypes col__dtypes df_obj df_obj',
      ⊢ df ∈ row__dtypes, col__dtypes ->
      df = DataFrame df_obj -> 
      df_obj' = Dataframe.InferDTypes axis df_obj ->
      ⊢ DataFrame df_obj' ∈ (get_row_dtypes df_obj'), (get_col_dtypes df_obj')
                                                                                            
where "'⊢' df '∈' rDT ',' cDT" := (has_dtype df rDT cDT).

Hint Constructors has_dtype : core.

Theorem progress : forall df rDT cDT,
    ⊢ df ∈ rDT, cDT ->
                dfvalue df \/ exists df', df --> df'.
Proof.
  intros df rDT cDT H.
  induction H; auto; try (right; destruct IHhas_dtype; destruct H0; eauto).
Qed.
  
Theorem preservation: forall df df' rDT cDT,
    ⊢ df ∈ rDT, cDT ->
    df --> df' ->
    ⊢ df' ∈ rDT, cDT.
Proof.
  intros df df' rDT cDT HT HE.
  generalize dependent df'.
  induction HT; intros df' HE; try (inversion HE; subst); eauto.
Qed.
