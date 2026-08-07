import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk118

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360333920353843556, 360333921123608815⟩, ⟨2940758949674718437, 2940765104006872387⟩, true⟩

def state01 : KState := ⟨⟨360390800391918710, 360390801163048823⟩, ⟨2269581227900187523, 2269587398344479995⟩, true⟩

def words00 : List Nat := [360583117387093832, 360583103386421550, 360583094842482011, 360583083405542664, 360583071970529005, 360583054379516957, 360583029649915851, 360583012034256046, 360582994421538294, 360582976217946747]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 11800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 11800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360395681030158229, 360395681802664700⟩, ⟨2211958282572347428, 2211964469278286446⟩, true⟩

def words01 : List Nat := [360582959947221779, 360582939446818347, 360582918949858289, 360582905560988464, 360582897584451000, 360582885080512884, 360582872578674637, 360582855163414883, 360582835070059023, 360582819236613794]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 11810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 11800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360472403235643057, 360472404009514270⟩, ⟨1304426355145200342, 1304432557989093972⟩, true⟩

def words02 : List Nat := [360582803405800077, 360582794673631729, 360582783124158450, 360582765922332613, 360582748723393631, 360582726132382271, 360582707371029536, 360582695703619887, 360582684038167197, 360582668807315546]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 11820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 11800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360615841021199497, 360615841796436237⟩, ⟨(-393094915843506005), (-393088696838496155)⟩, true⟩

def words03 : List Nat := [360582659487443124, 360582657255440394, 360582659877427997, 360582661070127659, 360582661070262304, 360582656110392409, 360582651151334349, 360582643209525773, 360582641737431776, 360582644541403850]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 11830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 11800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360429811048136542, 360429811824753379⟩, ⟨1810018228670600512, 1810024464022722654⟩, true⟩

def words04 : List Nat := [360582644541532962, 360582643787267973, 360582639388960664, 360582636961471964, 360582634534351144, 360582627855106159, 360582614092578199, 360582594804190328, 360582575519030969, 360582556505261626]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 11840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 11800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360316112567116133, 360316113345100592⟩, ⟨3157730487286844488, 3157736738852147766⟩, true⟩

def words05 : List Nat := [360582543616622268, 360582530524258734, 360582517434089864, 360582500676578386, 360582476844631374, 360582451189235942, 360582425538124923, 360582404360407636, 360582386786121968, 360582364334885765]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 11850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 11800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360457161191494975, 360457161970849707⟩, ⟨1484527194769938582, 1484533462593525818⟩, true⟩

def words06 : List Nat := [360582341887402911, 360582323005408308, 360582307662793290, 360582299371708154, 360582291082011564, 360582276346103197, 360582259664202110, 360582250029867725, 360582240397115750, 360582227974438042]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 11860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 11800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360324226763984803, 360324227544726269⟩, ⟨3063462996491265096, 3063469280782277894⟩, true⟩

def words07 : List Nat := [360582217439146008, 360582203321838734, 360582189206879576, 360582179059865329, 360582172553341236, 360582162792424288, 360582153033135354, 360582138556381049, 360582117037005538, 360582095329303902]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 11870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 11800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360448742425568070, 360448743207678619⟩, ⟨1583377847175509441, 1583384147738241927⟩, true⟩

def words08 : List Nat := [360582073625206214, 360582057981192216, 360582040513870573, 360582017973561147, 360581995437021231, 360581971094653769, 360581952091584714, 360581940113480685, 360581928137377044, 360581912606142727]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 11880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 11800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360489569490794324, 360489570274282159⟩, ⟨1097078979176610036, 1097085296121996554⟩, true⟩

def words09 : List Nat := [360581901407085881, 360581887710483473, 360581874016144169, 360581860139103130, 360581843566440817, 360581820806545221, 360581798050448142, 360581782308654961, 360581770063700755, 360581762315973084]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 11890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 11800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 11800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk118
