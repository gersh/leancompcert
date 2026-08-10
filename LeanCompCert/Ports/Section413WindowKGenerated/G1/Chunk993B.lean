import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk993A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk993B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk993A

def state06 : KState := ⟨⟨362486891333152573, 362487041864831727⟩, ⟨(-177677319474756042), (-167579347012303046)⟩, true⟩

def words05 : List Nat := [371285355307745357, 371285355255338189, 371285355235513485, 371285355239366166, 371285355254502713, 371285355277803378, 371285355299865607, 371285355303420671, 371285355272767926, 371285355294175109]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 99350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 99300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362478083234929166, 362478233797658821⟩, ⟨697537865921546484, 707638923727385876⟩, true⟩

def words06 : List Nat := [371285355399168317, 371285355402661187, 371285355372907511, 371285355325116564, 371285355276069115, 371285355212326920, 371285355096502875, 371285355083445340, 371285355069201412, 371285355050790827]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 99360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 99300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362495110339939775, 362495260934262501⟩, ⟨(-994507644675577755), (-984403447307318373)⟩, true⟩

def words07 : List Nat := [371285355011136822, 371285355045014404, 371285355160832183, 371285355187029040, 371285355196765877, 371285355207633036, 371285355318323033, 371285355380034521, 371285355482117905, 371285355585681713]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 99370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 99300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362488066070473965, 362488216696300574⟩, ⟨(-294443770228495311), (-284336441843723773)⟩, true⟩

def words08 : List Nat := [371285355683452078, 371285355698362043, 371285355755235111, 371285355813947980, 371285355868272657, 371285355871830426, 371285355855758030, 371285355839729664, 371285355876921569, 371285355909691689]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 99380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 99300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484512778282952, 362484663435668360⟩, ⟨58769349945248167, 68879815115385063⟩, true⟩

def words09 : List Nat := [371285356042103870, 371285356175986939, 371285356288954063, 371285356292448240, 371285356271761845, 371285356277447745, 371285356382542687, 371285356391874903, 371285356394493436, 371285356391554833]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 99390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 99300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 99300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk993B
