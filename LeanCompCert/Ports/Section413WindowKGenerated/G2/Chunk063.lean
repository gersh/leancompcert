import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk063

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360747129529151888, 360747129735080350⟩, ⟨(-1126398102845063056), (-1126397222662750060)⟩, true⟩

def state01 : KState := ⟨⟨360580916491224815, 360580916697838105⟩, ⟨(-78009244289953412), (-78008359789723916)⟩, true⟩

def words00 : List Nat := [360568418256045067, 360568462656361533, 360568487597803763, 360568512531341934, 360568521278936423, 360568542576162186, 360568550662205961, 360568558745699243, 360568558745764718, 360568556000676051]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 6300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 6300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361145619614423445, 361145619821724757⟩, ⟨(-3644160130848715559), (-3644159242003694711)⟩, true⟩

def words01 : List Nat := [360568582894979736, 360568609780784133, 360568650439635513, 360568708709307017, 360568745442766536, 360568782164601837, 360568843768567929, 360568921096791312, 360569012346648717, 360569103567650450]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 6310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 6300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360997539621374346, 360997539829371386⟩, ⟨(-2708899020826546914), (-2708898127581139182)⟩, true⟩

def words02 : List Nat := [360569174185938887, 360569233748219508, 360569318138398242, 360569402501913630, 360569466219515913, 360569505444560179, 360569526646409012, 360569547841566397, 360569593837569450, 360569661432975692]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 6320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 6300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360617578107427055, 360617578316111948⟩, ⟨(-301519589239063651), (-301518691635934019)⟩, true⟩

def words03 : List Nat := [360569735640361091, 360569809824324958, 360569871359547962, 360569908439157600, 360569928238337809, 360569948031288572, 360569992563321299, 360570012660246884, 360570020162781420, 360570027662960090]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 6330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 6300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360816163238157492, 360816163447534576⟩, ⟨(-1560878606141180232), (-1560877704146155026)⟩, true⟩

def words04 : List Nat := [360570042290221809, 360570076749285150, 360570135890606061, 360570195013299350, 360570232623208147, 360570261633318815, 360570293469450721, 360570325295574804, 360570355934994772, 360570394638820019]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 6340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 6300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360961273044209084, 360961273254284447⟩, ⟨(-2483606721211540824), (-2483605814778966634)⟩, true⟩

def words05 : List Nat := [360570417564336530, 360570440482643819, 360570488008622614, 360570548528882045, 360570594899291972, 360570641255126184, 360570670951998343, 360570707785549105, 360570769195273520, 360570830585713631]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 6350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 6300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360995796337327327, 360995796548095563⟩, ⟨(-2704002283030235139), (-2704001372187518579)⟩, true⟩

def words06 : List Nat := [360570916536913264, 360570978212895455, 360571019771876537, 360571061317805437, 360571089493985228, 360571130069670169, 360571195180168160, 360571260270234024, 360571306536685486, 360571373165237689]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 6360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 6300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361138336484267425, 361138336695730027⟩, ⟨(-3613125856302876422), (-3613124941033541802)⟩, true⟩

def words07 : List Nat := [360571449848020003, 360571526506759353, 360571627648443304, 360571704597523565, 360571757821790480, 360571811029370399, 360571863055813880, 360571927393033115, 360572016171980386, 360572104923118596]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 6370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 6300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361046142228810593, 361046142440974761⟩, ⟨(-3026241734889453099), (-3026240815140621035)⟩, true⟩

def words08 : List Nat := [360572181163680768, 360572233276141562, 360572291883141457, 360572350471806094, 360572402399235699, 360572443146583604, 360572471424951414, 360572499694475073, 360572552328974682, 360572626431721026]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 6380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 6300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360857130840580614, 360857131053440872⟩, ⟨(-1818075425477992199), (-1818074501277628025)⟩, true⟩

def words09 : List Nat := [360572686752457732, 360572747054336388, 360572794917153665, 360572833762752041, 360572866010408563, 360572898248002603, 360572954790029210, 360573012518952360, 360573056912539822, 360573101292266427]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 6390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 6300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 6300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk063
