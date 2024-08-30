signature serialiseLib =
sig
  include Abbrev

  val print_db : unit ->
    (hol_type * (term * (hol_type * (hol_type * hol_type list)) list)) list * thm list
  val extend_db : term * thm * thm -> term * thm * thm -> unit

  val define_ser_de : hol_type -> thm * thm * (thm list)
  val rec_define_ser_de : hol_type -> thm list

end
