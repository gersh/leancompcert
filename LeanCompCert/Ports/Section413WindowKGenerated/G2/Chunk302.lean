import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk302

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360625825848694958, 360625831337348823⟩, ⟨(-1280516605831665909), (-1280404507318281059)⟩, true⟩

def state01 : KState := ⟨⟨360603976907497305, 360603982399963652⟩, ⟨(-620812686897402815), (-620700473227777629)⟩, true⟩

def words00 : List Nat := [360583436097779209, 360583436098179897, 360583436722657216, 360583437581467759, 360583437681290705, 360583437681694092, 360583437631330851, 360583437034075868, 360583436436784696, 360583436887626167]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 30200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 30200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360526118706996237, 360526124203241180⟩, ⟨1731909742862094058, 1732022070702138456⟩, true⟩

def words01 : List Nat := [360583438660094588, 360583440432531070, 360583441628342066, 360583441734368858, 360583441734704372, 360583441562796306, 360583441390784809, 360583440905910601, 360583439867497641, 360583437971298829]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 30210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 30200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360621699381308679, 360621704881340227⟩, ⟨(-1156890949042799702), (-1156778506753500002)⟩, true⟩

def words02 : List Nat := [360583436075135171, 360583434904896742, 360583435106627949, 360583435753346814, 360583435753718856, 360583435761806520, 360583436870965740, 360583437980171704, 360583438969355502, 360583440235554329]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 30220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 30200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590618724134291, 360590624227992926⟩, ⟨(-217180877707642788), (-217068319706064032)⟩, true⟩

def words03 : List Nat := [360583440944500520, 360583441653440297, 360583442306259482, 360583443508021474, 360583444432066530, 360583445356115880, 360583445734113644, 360583445804639581, 360583446042347953, 360583446280183460]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 30230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 30200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360559091917136531, 360559097424770965⟩, ⟨736300174234756561, 736412846435537879⟩, true⟩

def words04 : List Nat := [360583447607730089, 360583447847776824, 360583447848135232, 360583447299765424, 360583446751366995, 360583445593374205, 360583445062023056, 360583444110264248, 360583443158527067, 360583441651099413]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 30240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 30200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360649048142800898, 360649053654220493⟩, ⟨(-1985469711593535902), (-1985356924872602624)⟩, true⟩

def words05 : List Nat := [360583440846684404, 360583440283592313, 360583440246209528, 360583440805266219, 360583440805636223, 360583440430579798, 360583440460625237, 360583441540558407, 360583443709161857, 360583445877713683]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 30250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 30200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360619344096035942, 360619349611284415⟩, ⟨(-1086865033794879743), (-1086752131193366711)⟩, true⟩

def words06 : List Nat := [360583447026807740, 360583447089791149, 360583447874189376, 360583448658655100, 360583449165705838, 360583449166107634, 360583449084297877, 360583448246083021, 360583447657368244, 360583448843843850]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 30260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 30200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360522262996799913, 360522268515829006⟩, ⟨1852511517727309457, 1852624534787418213⟩, true⟩

def words07 : List Nat := [360583451118078966, 360583453392243357, 360583455121245782, 360583455764874446, 360583455765216822, 360583455638313415, 360583455511299022, 360583455120673350, 360583453644869009, 360583451624639687]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 30270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 30200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575417601685521, 360575423124511342⟩, ⟨242798359623125162, 242911491666680130⟩, true⟩

def words08 : List Nat := [360583449604453223, 360583448427663795, 360583448118891085, 360583447978064734, 360583447837219647, 360583446781505837, 360583445275297357, 360583444409942611, 360583443544533218, 360583442652133220]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 30280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 30200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360572670298562440, 360572675825214481⟩, ⟨326093568045873796, 326206816004082682⟩, true⟩

def words09 : List Nat := [360583442387742277, 360583441419192318, 360583440568005186, 360583441664492241, 360583442311506222, 360583442958549815, 360583443061815241, 360583443062217224, 360583442081596260, 360583441726732768]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 30290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 30200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 30200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk302
