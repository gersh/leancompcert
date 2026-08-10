import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk799A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk799B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk799A

def state06 : KState := ⟨⟨360556826898210968, 360556868540838248⟩, ⟨2021059836124414656, 2023308676131656960⟩, true⟩

def words05 : List Nat := [360582173560755924, 360582173560996235, 360582173561110476, 360582173463792368, 360582173370244737, 360582173237990026, 360582173105391764, 360582173064072205, 360582172866573806, 360582172551295123]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 79950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 79900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360574457355736347, 360574499009171467⟩, ⟨611169568947179538, 613419273204205082⟩, true⟩

def words06 : List Nat := [360582172235781318, 360582171916610906, 360582171675278720, 360582171480815144, 360582171286277632, 360582170959803034, 360582170477084696, 360582170150899503, 360582169824361173, 360582169626568044]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 79960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 79900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360568256557580021, 360568298221897534⟩, ⟨1107072961903869804, 1109323536478823588⟩, true⟩

def words07 : List Nat := [360582169531673420, 360582169319338034, 360582169106789013, 360582169073338208, 360582169074313215, 360582168990594820, 360582168906748830, 360582168734342192, 360582168405720968, 360582168233606447]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 79970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 79900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360575193304248882, 360575234979351990⟩, ⟨552221420968977502, 554472858230530416⟩, true⟩

def words08 : List Nat := [360582168061121121, 360582167910455987, 360582167811101168, 360582167633284497, 360582167455288478, 360582167184584028, 360582166991662844, 360582166955058299, 360582166918352851, 360582166756552022]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 79980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 79900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360615200534631228, 360615242220527870⟩, ⟨(-2648203799003362951), (-2645951498313593885)⟩, true⟩

def words09 : List Nat := [360582166676536962, 360582166683534549, 360582166818313686, 360582166963156571, 360582166974294108, 360582166985540073, 360582167152596869, 360582167411253204, 360582167825613251, 360582168240223704]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 79990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 79900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 79900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk799B
