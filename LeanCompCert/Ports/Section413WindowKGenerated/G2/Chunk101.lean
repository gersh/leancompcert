import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk101

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360728682863894480, 360728683419391853⟩, ⟨(-1496708267194117450), (-1496704464158543626)⟩, true⟩

def state01 : KState := ⟨⟨360592024902645492, 360592025459307094⟩, ⟨(-116565929389250252), (-116562114589161848)⟩, true⟩

def words00 : List Nat := [360580515421812767, 360580515421934876, 360580517562724702, 360580523512398030, 360580524503234119, 360580524503356375, 360580520733233108, 360580512090819112, 360580503450090181, 360580497211399948]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 10100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 10100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360437710133568744, 360437710691381258⟩, ⟨1444971478622229724, 1444975305063915556⟩, true⟩

def words01 : List Nat := [360580508097813721, 360580518982097741, 360580524891519706, 360580528285740063, 360580528285844462, 360580522921548144, 360580518075282430, 360580518075404710, 360580508922804787, 360580494812435005]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 10110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 10100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360473512966669655, 360473513525638028⟩, ⟨1083013068342632645, 1083016906487318971⟩, true⟩

def words02 : List Nat := [360580480704825382, 360580471274224110, 360580473634514799, 360580477757494618, 360580477757608593, 360580473592076839, 360580464005139496, 360580451268745304, 360580438534832208, 360580425362408741]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 10120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 10100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360520462033327737, 360520462593462456⟩, ⟨606982084125568953, 606985934091120121⟩, true⟩

def words03 : List Nat := [360580414809578428, 360580396792937214, 360580378779828507, 360580370469011318, 360580367277552699, 360580361517511646, 360580355758591792, 360580344638973169, 360580329043079957, 360580323139230812]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 10130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 10100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360638331757574563, 360638332318865763⟩, ⟨(-588928148624843009), (-588924286926908725)⟩, true⟩

def words04 : List Nat := [360580321021868419, 360580323605222667, 360580323605334929, 360580318230170128, 360580312856045121, 360580304924069245, 360580307731951446, 360580312257456872, 360580312257566496, 360580315937531224]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 10140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 10100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360657820961316971, 360657821523766131⟩, ⟨(-787161542356478561), (-787157668899324295)⟩, true⟩

def words05 : List Nat := [360580331320147088, 360580346699769667, 360580357945832009, 360580359593605567, 360580359593718704, 360580353131799286, 360580346671130684, 360580339778270066, 360580345375125408, 360580353000107109]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 10150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 10100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360734066938107558, 360734067501728493⟩, ⟨(-1563234084094522805), (-1563230198726501527)⟩, true⟩

def words06 : List Nat := [360580355826367821, 360580355826490691, 360580351965072415, 360580354859478461, 360580354859581640, 360580355353720664, 360580355353830255, 360580352872257232, 360580357550876890, 360580372663588045]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 10160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 10100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360538596145106628, 360538596709887118⟩, ⟨425530953530496825, 425534850697110343⟩, true⟩

def words07 : List Nat := [360580387349230940, 360580402032008334, 360580411787858517, 360580411975449506, 360580411975553395, 360580404524286625, 360580399250088839, 360580401882130870, 360580401882242191, 360580397775770921]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 10170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 10100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360730102315204930, 360730102881147162⟩, ⟨(-1524769048795941165), (-1524765139796889393)⟩, true⟩

def words08 : List Nat := [360580399183542501, 360580409522393342, 360580422679940342, 360580435834927007, 360580439184037465, 360580441307463626, 360580449289389308, 360580457269785064, 360580469403120157, 360580484086151883]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 10180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 10100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360581851552496107, 360581852119613940⟩, ⟨(-12770971037250344), (-12767050052995988)⟩, true⟩

def words09 : List Nat := [360580492814229768, 360580501540611121, 360580519857868927, 360580542970283957, 360580563547427193, 360580584120554530, 360580596978872794, 360580600325072657, 360580600447899348, 360580600570740987]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 10190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 10100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 10100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk101
