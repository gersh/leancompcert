import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk188A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360686991452900953, 360686993493033617⟩, ⟨(-1904833208518442425), (-1904807248681014425)⟩, true⟩

def state01 : KState := ⟨⟨360694395348528369, 360694397390948171⟩, ⟨(-2044122890548029865), (-2044096887701184569)⟩, true⟩

def words00 : List Nat := [360585683305282325, 360585688656078948, 360585696825164530, 360585704993451153, 360585712441721148, 360585717078001382, 360585720294715503, 360585723511113865, 360585726636406608, 360585732413663541]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 18800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 18800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360582003321701773, 360582005366378986⟩, ⟨70745601660583841, 70771646980968547⟩, true⟩

def words01 : List Nat := [360585738969511259, 360585745524706936, 360585750662344557, 360585754602074305, 360585757193703976, 360585759785125842, 360585763984182678, 360585766014566195, 360585766014782698, 360585765815209006]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 18810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 18800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360585770578064877, 360585772625010313⟩, ⟨(-467093490411370), (-441005470762756)⟩, true⟩

def words02 : List Nat := [360585765615604013, 360585764673914522, 360585764829548821, 360585764985210239, 360585764985431650, 360585762698608748, 360585757607138919, 360585754412284845, 360585751217698272, 360585749205889143]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 18820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 18800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360562381979449460, 360562384028680192⟩, ⟨440079349489709679, 440105480552890759⟩, true⟩

def words03 : List Nat := [360585749206102998, 360585747794829498, 360585746534213160, 360585748405942336, 360585749563570095, 360585750721114728, 360585750721335537, 360585749477947461, 360585745431907612, 360585744192191492]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 18830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 18800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360556126880353438, 360556128931846948⟩, ⟨557721708409353232, 557747882114403690⟩, true⟩

def words04 : List Nat := [360585743652042336, 360585743652282601, 360585741549792069, 360585737265164133, 360585732980947757, 360585727985488694, 360585724484097628, 360585722804284636, 360585721124623028, 360585717678908721]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 18840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 18800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk188A
