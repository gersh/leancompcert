import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk601A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360572972614485019, 360572995613317786⟩, ⟨554785452738686217, 555719249039123405⟩, true⟩

def state01 : KState := ⟨⟨360612492076846394, 360612515083625797⟩, ⟨(-1820421610550798958), (-1819487336618579838)⟩, true⟩

def words00 : List Nat := [360582242159737021, 360582242501920971, 360582243120723853, 360582243739673054, 360582244123936761, 360582244349119923, 360582244851015239, 360582245353140731, 360582245787519309, 360582246291946761]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 60100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 60100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360600462981041122, 360600485995838858⟩, ⟨(-1097273402741267803), (-1096338646788035275)⟩, true⟩

def words01 : List Nat := [360582246657475467, 360582247023083329, 360582247574293364, 360582248295074473, 360582248837354011, 360582249379764681, 360582249753497036, 360582249851759514, 360582250155768818, 360582250460056220]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 60110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 60100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360608320686090456, 360608343708824616⟩, ⟨(-1569779107745466705), (-1568843874615238523)⟩, true⟩

def words02 : List Nat := [360582250948624574, 360582251309280722, 360582251453537206, 360582251597867700, 360582251598576353, 360582251715184970, 360582252156819238, 360582252598600160, 360582252840241574, 360582253275028151]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 60120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 60100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360628295278958929, 360628318309631287⟩, ⟨(-2770957217810774710), (-2770021507317420496)⟩, true⟩

def words03 : List Nat := [360582253926372113, 360582254577941390, 360582255505887516, 360582256221825002, 360582256704348857, 360582257186920863, 360582257499114554, 360582257989362105, 360582258755927368, 360582259522658716]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 60130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 60100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360630394796385938, 360630417835069921⟩, ⟨(-2897408132856307430), (-2896471940504328518)⟩, true⟩

def words04 : List Nat := [360582260150220366, 360582260502515621, 360582261071345604, 360582261640419764, 360582262062922760, 360582262538777736, 360582262829400857, 360582263120104757, 360582263687134566, 360582264488650006]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 60140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 60100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk601A
