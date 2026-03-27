open! IStd
open! Vocab

let pdesc_has_annot pdesc ~annot_name =
  let ProcAttributes.{method_annotation= {return}} = Procdesc.get_attributes pdesc in
  List.exists return ~f:(fun (Annot.{class_name}, _) -> String.( = ) annot_name class_name)


let rec is_model procname = is_before procname || is_before_class procname

and is_before procname =
  Option.value_map
    ~f:(fun pdesc ->
      pdesc_has_annot pdesc ~annot_name:"org.junit.Before"
      || String.equal "setUp" (Procname.get_method procname) )
    ~default:false (Procdesc.load procname)


and is_before_class procname =
  Option.value_map
    ~f:(fun pdesc -> pdesc_has_annot pdesc ~annot_name:"org.junit.BeforeClass")
    ~default:false (Procdesc.load procname)
