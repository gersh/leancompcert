import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk483A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk483B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk483A

def state06 : KState := ⟨⟨360529175677831741, 360529190309532523⟩, ⟨2569968707049405481, 2570446848424276295⟩, true⟩

def words05 : List Nat := [360582350939481712, 360582349792786304, 360582348646010842, 360582347925800386, 360582347421390246, 360582346713683479, 360582346005923305, 360582345087527859, 360582343741396943, 360582342643040056]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 48350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 48300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360509776673968195, 360509791311942110⟩, ⟨3508136063967047769, 3508614508742359747⟩, true⟩

def words06 : List Nat := [360582341544503802, 360582340774567707, 360582339576990371, 360582338042144036, 360582336507253962, 360582334710280335, 360582333128818587, 360582331613244209, 360582330097660573, 360582328308194795]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 48360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 48300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360540108148399852, 360540122792653622⟩, ⟨2040825305597118986, 2041304054159302940⟩, true⟩

def words07 : List Nat := [360582326809136184, 360582325736347928, 360582324663410864, 360582323638915351, 360582322509535302, 360582321006793705, 360582319503996010, 360582317991724568, 360582316802881239, 360582315931433269]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 48370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 48300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360536414244746372, 360536428895338995⟩, ⟨2219487997900886295, 2219967053169353209⟩, true⟩

def words08 : List Nat := [360582315059924811, 360582313975987222, 360582312759738803, 360582311969528849, 360582311179155040, 360582310282126355, 360582309264860770, 360582308017112372, 360582306769291789, 360582305461843839]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 48380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 48300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360498013449011378, 360498028105884715⟩, ⟨4077843104778074355, 4078322464001404067⟩, true⟩

def words09 : List Nat := [360582304514352680, 360582303440473150, 360582302366570975, 360582301039095073, 360582299284478511, 360582297423418743, 360582295562240221, 360582294126823029, 360582292707020516, 360582290966711191]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 48390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 48300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 48300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk483B
