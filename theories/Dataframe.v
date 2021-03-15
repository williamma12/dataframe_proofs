Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Datatypes.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Program.Wf.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Section Dataframe_Cell.
  
  (* Define a dataframe cell value. *)
  Inductive data_value : Type :=
  | DV_String : option string -> data_value
  | DV_Nat : option nat -> data_value.

  Hint Constructors data_value : Dataframes.

  Definition data_value_eqb (val1 val2: data_value) : bool :=
    match val1, val2 with
    | DV_String (Some s1), DV_String (Some s2) => eqb s1 s2
    | DV_String (None), DV_String (None) => true
    | DV_Nat (Some n1), DV_Nat (Some n2) => Nat.eqb n1 n2
    | DV_Nat (None), DV_Nat (None) => true
    | _, _ => false
    end.

  (* Define dataframe data types for the cells. *)
  Inductive dtype : Type :=
  | DF_String
  | DF_Nat.

  Definition dtype_eqb (dtype1 dtype2: dtype) : bool :=
    match dtype1, dtype2 with
    | DF_String, DF_String => true
    | DF_Nat, DF_Nat => true
    | _, _ => false
    end.

  Fixpoint dtype_eqb_lsts (l1 l2: list dtype) : bool :=
    match l1, l2 with
    | h1 :: t1, h2 :: t2 =>
      if negb (dtype_eqb h1 h2)
      then false
      else dtype_eqb_lsts t1 t2
    | _, _ => false
    end.

  Hint Constructors dtype : Dataframes.

  (* Infer dtype from value. *)
  Definition infer_dtype (val: data_value) : dtype :=
    match val with
    | DV_String _ => DF_String
    | DV_Nat _ => DF_Nat
    end.

  Example infer_dtype1 : infer_dtype (DV_String (@None string)) = DF_String.
  Proof. reflexivity. Qed.
  Example infer_dtype2 : infer_dtype (DV_Nat (Some 3)) = DF_Nat.
  Proof. reflexivity. Qed.

  (* Define helper function to get the "parent data type" of two data types. *)
  Fixpoint parent_dtype_lst (l : list dtype) : dtype :=
    match l with
    | DF_String :: _ => DF_String
    | DF_Nat :: t => parent_dtype_lst t
    | nil => DF_Nat
    end.

  Example parent_dtype1 : parent_dtype_lst [DF_String ; DF_Nat] = DF_String.
  Proof. reflexivity. Qed.
  Example parent_dtype2 : parent_dtype_lst [DF_Nat ; DF_Nat] = DF_Nat.
  Proof. reflexivity. Qed.

  Definition parent_dtype (d1 d2: dtype) : dtype := parent_dtype_lst [d1;d2].
  Definition parent_dtype_pair (dtype_pair: dtype * dtype) : dtype :=
    parent_dtype (fst dtype_pair) (snd dtype_pair).

  Definition infer_dtypes (l: list data_value) : dtype :=
    fold_left parent_dtype (map infer_dtype l) DF_Nat.

  Example infer_dtypes1 : infer_dtypes [DV_Nat (Some 4) ; DV_String (@None string)] = DF_String.
  Proof. reflexivity. Qed.
  Example infer_dtypes2 : infer_dtypes [DV_Nat (Some 4)] = DF_Nat.
  Proof. reflexivity. Qed.

End Dataframe_Cell.

Section Dataframe_Index.

  Inductive Index : Type :=
    DF_Index : nat -> data_value -> Index.

  Hint Constructors Index : Dataframes.

  Definition position (index: Index) : nat := match index with DF_Index pos _ => pos end.

  Example position1 : position (DF_Index 0 (DV_Nat None)) = 0.
  Proof. reflexivity. Qed.

  Definition label (index: Index) : data_value := match index with DF_Index _ label => label end.

  Example label1 : label (DF_Index 0 (DV_Nat None)) = DV_Nat None.
  Proof. reflexivity. Qed.

  Definition label_dtypes (index: list Index) : list dtype := map (fun ind => infer_dtype (label ind)) index.

  Example label_dtypes1 : label_dtypes [DF_Index 0 (DV_Nat None); DF_Index 1 (DV_String None)] = [DF_Nat; DF_String].
  Proof. reflexivity. Qed.

  Definition increment_positions (n: nat) (index: list Index) : list Index :=
    map (fun ind => DF_Index (n + (position ind)) (label ind)) index.

  Example increment_positions1 :
    increment_positions 10 [DF_Index 0 (DV_Nat None); DF_Index 1 (DV_String None)] = [DF_Index 10 (DV_Nat None); DF_Index 11 (DV_String None)].
  Proof. reflexivity. Qed.

  Fixpoint valid_index (l: list Index) : bool :=
    match l with
    | index :: t =>
      if (existsb (fun ind => Nat.eqb (position ind) (position index)) t)
      then false
      else valid_index t
    | nil => true
    end.

End Dataframe_Index.

Section Transpose_Helper.

  Definition matrix_length {T: Type} (mat: list (list T)) : nat :=
    Datatypes.length mat.
  
  Example matrix_length1 : matrix_length [[1;2];[3;4]] = 2.
  Proof. reflexivity. Qed.

  Definition matrix_width {T: Type} (mat: list (list T)) : nat :=
    match mat with
    | h :: _ => Datatypes.length h
    | _ => 0
    end.

  Example matrix_width1 : matrix_width [[1;2];[3;4]] = 2.
  Proof. reflexivity. Qed.
  
  Definition valid_matrix {T: Type} (mat: list (list T)) : bool :=
    forallb (fun row => Nat.eqb (matrix_width mat) (Datatypes.length row)) mat.

  Example valid_matrix1 : valid_matrix [[1;2];[3;4]] = true.
  Proof. reflexivity. Qed.
  Example valid_matrix2 : valid_matrix [[1;2];[3]] = false.
  Proof. reflexivity. Qed.

  Fixpoint get_nth_row {T: Type} (n: nat) (ls: list (list T)) : list T :=
    match ls with
    | h__row :: t__rows => if Nat.eqb n 0 then h__row else get_nth_row (n - 1) t__rows
    | nil => nil
    end.

  Example get_nth_row1 : get_nth_row 1 [[1;2];[3;4]] = [3;4].
  Proof. reflexivity. Qed.

  (* 
     Helper functions for transpose.
     Source : https://coq.discourse.group/t/proving-matrix-transpose-function/803/4
   *)

  Fixpoint get_nth_column {T: Type} (n: nat) (mat: list (list T)) (default: T) : list T := 
    match mat with 
    | row :: t => (nth n row default) :: (get_nth_column n t default)
    | nil => nil
    end. 
  
  Fixpoint remove_first_column {T: Type} (ls: list (list T)) : list (list T) :=
    match ls with
    | (h :: t__row) :: t__rows => t__row :: (remove_first_column t__rows)
    | nil :: t__rows => remove_first_column t__rows
    | nil => nil
    end.

  Fixpoint get_first_column {T: Type} (ls: list (list T)) : (list T) :=
    match ls with
    | (h :: t__row) :: t__rows => h :: (get_first_column t__rows)
    | nil :: t__rows => get_first_column t__rows
    | nil => nil
    end.

  Definition matrix_size {T: Type} (ls : list (list T)) : nat :=
    List.fold_right (fun b a => S (Datatypes.length b + a)) 0 ls.

  Lemma matrix_size_cons (T: Type) (x : list T) (l : list (list T)) :
    matrix_size (x :: l) = S (Datatypes.length x + matrix_size l).
  Proof. reflexivity. Qed.

  Lemma matrix_size_remove_first_column_le (T: Type) (l : list (list T)) :
    matrix_size (remove_first_column l) <= matrix_size l.
  Proof.
    induction l.
    - reflexivity.
    - induction a.
      + simpl. auto.
      + simpl. lia.
  Qed.

  Program Fixpoint transpose_matrix {T: Type} (ls: list (list T)) {measure (matrix_size ls)} : list (list T) :=
    match ls with
    | (h :: t__row) :: t__rows => (h :: get_first_column t__rows) :: (transpose_matrix (t__row :: (remove_first_column t__rows)))
    | nil :: t__rows => transpose_matrix t__rows
    | nil => nil
    end.
  Next Obligation.
    rewrite matrix_size_cons; cbn.
    pose proof matrix_size_remove_first_column_le _ t__rows.
    lia.
  Qed.

  Example transpose_matrix1 : transpose_matrix [[1;2];[3;4]] = [[1;3];[2;4]].
  Proof. reflexivity. Qed.

  Definition transpose_def {T: Type} (mat transMat: list (list T)) :=
    forall default n,
      get_nth_column n mat default = get_nth_row n transMat /\
      get_nth_row n mat = get_nth_column n transMat default.

  Theorem transpose_matrix_eq_transpose_def : forall T mat,
      @valid_matrix T mat = true ->
      transpose_def mat (transpose_matrix mat).
  Proof.
  Admitted.
  
  Lemma transpose_valid : forall T mat,
      @valid_matrix T mat = true ->
      valid_matrix (transpose_matrix mat) = true.
  Proof.
  Admitted.
  
  Lemma transpose_length_width_eq : forall T mat,
      @valid_matrix T mat = true ->
      matrix_length (transpose_matrix mat) = matrix_width mat.
  Proof.
  Admitted.

  Lemma transpose_width_length_eq : forall T mat,
      @valid_matrix T mat = true ->
      matrix_width (transpose_matrix mat) = matrix_length mat.
  Proof.
  Admitted.

End Transpose_Helper.

Section Dataframe.

  Inductive DataFrame : Type :=
    ValidDF : forall
      (row__index: list Index)
      (row__dtypes: list dtype)
      (col__index: list Index)
      (col__dtypes: list dtype)
      (values: list (list data_value)),
      (*
      (** Validate lengths **)
      Nat.eqb (Datatypes.length row__index) (Datatypes.length row__dtypes) = true ->
      Nat.eqb (Datatypes.length col__index) (Datatypes.length col__dtypes) = true ->
      valid_matrix values = true ->
      Nat.eqb (matrix_length values) (Datatypes.length row__index) = true ->
      Nat.eqb (matrix_width values) (Datatypes.length col__index) = true ->
      (** Validate dtypes **)
      dtype_eqb_lsts (map infer_dtypes values) row__dtypes = true ->
      dtype_eqb_lsts (map infer_dtypes (transpose_matrix values)) col__dtypes = true ->
      (** Validate index positions distinct. **)
      valid_index row__index = true ->
      valid_index col__index = true ->
       *)
      DataFrame.

  Check ValidDF.

  Hint Constructors DataFrame : Dataframes.

  Definition get_row_index (df: DataFrame) : list Index :=
    match df with
      ValidDF row__index _ _ _ _ (* _ _ _ _ _ _ _ _ _ *) => row__index
    end.

  Definition set_row_index (row__index: list Index) (df: DataFrame) : DataFrame :=
    match df with
      ValidDF _ row__dtypes col__index col__dtypes values =>
      ValidDF row__index row__dtypes col__index col__dtypes values
    end.
  
  Definition get_row_dtypes (df: DataFrame) : list dtype :=
    match df with
      ValidDF _ row__dtypes _ _ _ (* _ _ _ _ _ _ _ _ _ *) => row__dtypes
    end.

  Definition set_row_dtypes (row__dtypes: list dtype) (df: DataFrame) : DataFrame :=
    match df with
      ValidDF row__index _ col__index col__dtypes values =>
      ValidDF row__index row__dtypes col__index col__dtypes values
    end.
  
  Definition get_col_index (df: DataFrame) : list Index :=
    match df with
      ValidDF _ _ col__index _ _ (* _ _ _ _ _ _ _ _ _ *) => col__index
    end.

  Definition set_col_index (col__index: list Index) (df: DataFrame) : DataFrame :=
    match df with
      ValidDF row__index row__dtypes _ col__dtypes values =>
      ValidDF row__index row__dtypes col__index col__dtypes values
    end.
  
  Definition get_col_dtypes (df: DataFrame) : list dtype :=
    match df with
      ValidDF _ _ _ col__dtypes _ (* _ _ _ _ _ _ _ _ _ *) => col__dtypes
    end.

  Definition set_col_dtypes (col__dtypes: list dtype) (df: DataFrame) : DataFrame :=
    match df with
      ValidDF row__index row__dtypes col__index _ values =>
      ValidDF row__index row__dtypes col__index col__dtypes values
    end.
  
  Definition get_values (df: DataFrame) : list (list data_value) :=
    match df with
      ValidDF _ _ _ _ values (* _ _ _ _ _ _ _ _ _ *) => values
    end.

  Definition set_values (values: list (list data_value)) (df: DataFrame) :=
    match df with
      ValidDF row__index row__dtypes col__index col__dtypes _ =>
      ValidDF row__index row__dtypes col__index col__dtypes values
    end.
  
  Definition length (df: DataFrame) : nat :=
    match df with
      ValidDF row__index _ _ _ _ (* _ _ _ _ _ _ _ _ _ *) => Datatypes.length row__index
    end.

  Definition width (df: DataFrame) : nat :=
    match df with
      ValidDF _ _ col__index _ _ (* _ _ _ _ _ _ _ _ _ *) => Datatypes.length col__index
    end.

End Dataframe.

Section DataFrame_Axis.

  (* Axis argument for which axis to apply the function. *)
  Inductive Axis : Type := Columns | Rows.

  Definition other_axis (axis : Axis) : Axis :=
    match axis with
    | Columns => Rows
    | Rows => Columns
    end.

  Definition get_axis_index (axis: Axis) (df: DataFrame) : list Index :=
    match axis with
    | Columns => get_col_index df
    | Rows => get_row_index df
    end.

  Definition set_axis_index (axis_index: list Index) (axis: Axis) (df: DataFrame) : DataFrame :=
    match axis with
    | Columns => set_col_index axis_index df
    | Rows => set_row_index axis_index df
    end. 

  Definition get_axis_dtypes (axis: Axis) (df: DataFrame) : list dtype :=
    match axis with
    | Columns => get_col_dtypes df
    | Rows => get_row_dtypes df
    end.

  Definition set_axis_dtypes (axis_dtypes: list dtype) (axis: Axis) (df: DataFrame) : DataFrame :=
    match axis with
    | Columns => set_col_dtypes axis_dtypes df
    | Rows => set_row_dtypes axis_dtypes df
    end.

  Definition get_axis_values (axis: Axis) (df: DataFrame) : list (list data_value) :=
    match axis with
    | Rows => get_values df
    | Columns => transpose_matrix (get_values df)
    end.

  Definition set_axis_values (axis_values: list (list data_value)) (axis: Axis) (df: DataFrame) : DataFrame :=
    match axis with
    | Rows => set_values axis_values df
    | Columns => set_values (transpose_matrix axis_values) df
    end.

  Definition axis_length (axis: Axis) (df: DataFrame) : nat :=
    match axis with
    | Columns => width df
    | Rows => length df
    end.

End DataFrame_Axis.

Section Transpose.

  Definition Transpose (df: DataFrame) : DataFrame :=
    match df with
    | ValidDF row__index row__dtypes col__index col__dtypes values
      (*
              row__validMetadata col__validMetadata
              values__valid row__validValues col__validValues
              row__validDtypes col__validDtypes
              row__validIndex col__validIndex 
       *)
      =>
      ValidDF col__index col__dtypes row__index row__dtypes (transpose_matrix values)
    (*
              col__validMetadata row__validMetadata
              (transpose_valid data_value values values__valid) col__validValues row__validValues
              col__validDtypes row__validDtypes
              col__validIndex row__validIndex
     *)
    end.
  
End Transpose.

Section Mask.

  Fixpoint filter_option {T: Type} (l: list (option T)) : list T :=
    match l with
    | Some h :: t => h :: filter_option t
    | None :: t => filter_option t
    | nil => nil
    end.

  Definition reorder_lst {T: Type} (l: list T) (order: list nat) : list T :=
    filter_option (map (nth_error l) order).

  (* 
     Apply a mask over a dataframe. 
     Mask is a list of natural numbers corresponding to index positions.
   *)
  Definition Mask (mask_positions: list nat) (axis: Axis) (df: DataFrame) : DataFrame :=
    set_values
      (reorder_lst (get_values df) mask_positions)
      (set_axis_index (reorder_lst (get_axis_index axis df) mask_positions) axis df).
  
End Mask.

Section Filter.

  Fixpoint filter_other {A B: Type} (filter_func: A -> bool) (input_list: list A) (filter_list: list B) : list B :=
    match input_list, filter_list with
    | h__input :: t__input, h__filter :: t__filter =>
      if filter_func h__input
      then h__filter :: filter_other filter_func t__input t__filter
      else filter_other filter_func t__input t__filter
    | _, _ => nil
    end.

  Example filter_other1 : filter_other (Nat.eqb 5) [1;2;3;5;5] [1;2;3;4;5] = [4;5].
  Proof. reflexivity. Qed.

  (* 
     Filter rows/columns if they satisfy some filter function.
   *)
  Definition Filter (filter_func: list data_value -> bool) (axis: Axis) (df: DataFrame) : DataFrame :=
    set_values (filter_other filter_func (get_values df) (get_values df))
               (set_axis_dtypes (filter_other filter_func (get_values df) (get_axis_dtypes axis df)) axis
                                (set_axis_index (filter_other filter_func (get_values df) (get_axis_index axis df)) axis
                                                df)).

End Filter.

Section ToFromLabels.

  Fixpoint reenumerate_index_helper (original_length: nat) (l: list Index) : list Index :=
    match original_length - (Datatypes.length l), l with
    | pos, h__index :: t__index => (DF_Index pos (label h__index)) :: reenumerate_index_helper original_length t__index
    | _, _ => nil
    end.

  Definition reenumerate_index (l: list Index) : list Index := reenumerate_index_helper (Datatypes.length l) l.

  Example reenumerate_index1 :
    reenumerate_index [DF_Index 99 (DV_Nat (Some 0)); DF_Index 12 (DV_Nat (Some 1))] = [DF_Index 0 (DV_Nat (Some 0)); DF_Index 1 (DV_Nat (Some 1))].
  Proof. reflexivity. Qed.

  Definition enumerate_index_values (l: list data_value) : list Index := reenumerate_index_helper (Datatypes.length l) (map (fun label => DF_Index 0 label) l).

  Example enumerate_index_values1 :
    enumerate_index_values [DV_Nat (Some 0); DV_Nat (Some 1)] = [DF_Index 0 (DV_Nat (Some 0)); DF_Index 1 (DV_Nat (Some 1))].
  Proof. reflexivity. Qed.

  (* TODO: Update to match label_ind with actual index position. *)
  Definition ToLabels (label_ind: nat) (axis: Axis) (df: DataFrame) : DataFrame :=
    (set_axis_index
       (enumerate_index_values (get_nth_row label_ind (get_axis_values axis df)))
       axis
       df
    ).

  Definition FromLabels (axis: Axis) (df: DataFrame) : DataFrame :=
    (set_axis_values
       ((map label (get_axis_index axis df)) :: (get_axis_values (other_axis axis) df))
       (other_axis axis)
       (set_axis_dtypes  (** Set self axis dtypes to be parent of (label dtypes and original dtypes) **)
          (map
             parent_dtype_pair
             (combine
                (get_axis_dtypes axis df)
                (label_dtypes (get_axis_index axis df))))
          axis
          (set_axis_dtypes (** Update other axis dtypes to include parent of axis label dtypes **)
             (parent_dtype_lst
                (label_dtypes (get_axis_index axis df)) :: (get_axis_dtypes (other_axis axis) df))
             (other_axis axis)
             df))).

End ToFromLabels.

Section Map.
  
  Definition Map (map_func: (list data_value) -> (list data_value)) (map_dtypes: list (list dtype)) (axis: Axis) (df: DataFrame) : DataFrame :=
    (set_axis_values
       (map map_func (get_axis_values axis df))
       axis
       (set_axis_dtypes (** Update axis dtypes based on args. **)
          (map parent_dtype_lst map_dtypes)
          axis
          (set_axis_dtypes (** Update other axis dtypes. **)
             (repeat
                (parent_dtype_lst (map parent_dtype_lst map_dtypes))
                (Datatypes.length (get_axis_dtypes (other_axis axis) df)))
             (other_axis axis)
             df))).

End Map.

Section Concat.

  (* How to "combine" dataframes. *)
  Inductive Set_Combine : Type := Union | Intersection | Difference.

  (* Helper functions for intersction and difference. *)
  Definition index_eqb (ind1 ind2: Index) : bool := data_value_eqb (label ind1) (label ind2).

  Example index_eqb1 : index_eqb (DF_Index 0 (DV_Nat (Some 0))) (DF_Index 12 (DV_Nat (Some 0))) = true.
  Proof. reflexivity. Qed.
  Example index_eqb2 : index_eqb (DF_Index 0 (DV_Nat (Some 0))) (DF_Index 12 (DV_Nat (Some 3))) = false.
  Proof. reflexivity. Qed.

  Fixpoint lst_merge_other {A B: Type} (set_combine: Set_Combine) (eqb_func: A -> A -> bool) (ls1 ls2: list A) (other: list B) : list B :=
    match ls1, other with
    | h :: t, h__other :: t__other =>
      match set_combine with
      | Intersection =>
        if existsb (eqb_func h) ls2
        then
          h__other :: lst_merge_other set_combine eqb_func t ls2 t__other
        else
          lst_merge_other set_combine eqb_func t ls2 t__other
      | Difference =>
        if negb (existsb (eqb_func h) ls2)
        then
          h__other :: lst_merge_other set_combine eqb_func t ls2 t__other
        else
          lst_merge_other set_combine eqb_func t ls2 t__other
      | Union => h__other :: lst_merge_other set_combine eqb_func t ls2 t__other
      end
    | _, _ => nil
    end.

  Example lst_merge_other1 : lst_merge_other Intersection Nat.eqb [1;2] [1] [6;7] = [6].
  Proof. reflexivity. Qed.
  Example lst_merge_other2 : lst_merge_other Difference Nat.eqb [1;2] [1] [6;9] = [9].
  Proof. reflexivity. Qed.

  Definition ConcatUnion (axis: Axis) (other self: DataFrame) : DataFrame :=
    (set_axis_index (** Merge axis indexes. **)
       ((get_axis_index axis self) ++ (increment_positions (axis_length axis self) (get_axis_index axis other)))
       axis
       (set_axis_dtypes
          ((get_axis_dtypes axis self) ++ (get_axis_dtypes axis other))
          axis
          (set_axis_dtypes (** Set other axis dtypes. **)
             (map
                parent_dtype_pair
                (combine (get_axis_dtypes (other_axis axis) self) (get_axis_dtypes (other_axis axis) other)))
             (other_axis axis)
             (set_axis_values
                ((get_axis_values axis self) ++ (get_axis_values axis other))
                axis
                self)))).

  (* 
     Calculates intersection/difference based on index labels.
   *)
  Definition ConcatIntersectionDifference (set_combine: Set_Combine) (axis: Axis) (other self: DataFrame) : DataFrame :=
    (set_axis_index
       (lst_merge_other
          set_combine
          index_eqb
          (get_axis_index axis self)
          (get_axis_index axis other)
          (get_axis_index axis self))
       axis
       (set_axis_dtypes
          (lst_merge_other
             set_combine
             index_eqb
             (get_axis_index axis self)
             (get_axis_index axis other)
             (get_axis_dtypes axis self))
          axis
          (set_axis_values
             (lst_merge_other
                set_combine
                index_eqb
                (get_axis_index axis self)
                (get_axis_index axis other)
                (get_axis_values axis self))
             axis
             self))).

End Concat.

Section InferDtypes.

  Definition InferDTypes (axis: Axis) (df: DataFrame) : DataFrame :=
    (set_axis_dtypes
       (map infer_dtypes (get_axis_values axis df))
       axis
       df).

  Check InferDTypes.
End InferDtypes.
