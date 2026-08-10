import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk302A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk302A
