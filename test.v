Inductive day: Type :=
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday
    .

Definition next_weekday(d: day): day :=
    match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => saturday
    | saturday => sunday
    | sunday => monday
    end.


Example test_next_weekday:
    (next_weekday monday) = tuesday.

Proof. 
    simpl. 
    reflexivity. 
Qed.

Inductive bool: Type :=
    | true
    | false.

Definition negb(b: bool) :=
    match b with
    | true => false
    | false => true
    end.

Definition andb(b1: bool) (b2: bool) :=
    match b1 with
    | true => b2
    | false => false
    end.

Definition orb(b1: bool) (b2: bool) :=
    match b1 with
    | true => true
    | false => b2
    end.

Example test_orb:
    (orb false true) = true.
Proof.
    simpl.
    reflexivity.
Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_andb:
    true && false = false.
Proof.
    simpl.
    reflexivity.
Qed.