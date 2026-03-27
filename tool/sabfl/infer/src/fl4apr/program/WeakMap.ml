open! IStd

module Make (Key : PrettyPrintable.PrintableOrderedType) (Value : AbstractDomain.WithBottom) =
struct
  include AbstractDomain.Map (Key) (Value)

  let find loc m = try find loc m with _ -> Value.bottom

  let weak_update loc v reg = add loc (Value.join v (find loc reg)) reg

  let strong_update loc v reg = add loc v reg

  let update ~is_weak = if is_weak then weak_update else strong_update
end
