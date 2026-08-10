import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk677A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360590838536297092, 360590867997664118⟩, ⟨(-542886698382693281), (-541539420251308503)⟩, true⟩

def state01 : KState := ⟨⟨360581483892975655, 360581513363444390⟩, ⟨90311367355201748, 91659261716960562⟩, true⟩

def words00 : List Nat := [360582869020538508, 360582869021494661, 360582868813354842, 360582868767253421, 360582868720881378, 360582868531875571, 360582868193565009, 360582867745411303, 360582867297087792, 360582867066910894]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 67700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 67700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360543807480944855, 360543836960436298⟩, ⟨2641532373990052355, 2642880879323592799⟩, true⟩

def words01 : List Nat := [360582867047707322, 360582866931965250, 360582866816120977, 360582866591312923, 360582866148485725, 360582865609456188, 360582865070145451, 360582864595199708, 360582864128768378, 360582863553456434]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 67710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 67700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566740074018834, 360566769562535185⟩, ⟨1088455399020089662, 1089804515564186352⟩, true⟩

def words02 : List Nat := [360582862977944842, 360582862583307487, 360582862298098365, 360582862230800856, 360582862163456042, 360582861886941420, 360582861392460767, 360582860869242553, 360582860345756414, 360582859987982759]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 67720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 67700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360559835325493058, 360559864823128488⟩, ⟨1556180074066014903, 1557529808290090143⟩, true⟩

def words03 : List Nat := [360582859751271429, 360582859393516080, 360582859035570935, 360582858895593508, 360582858892689059, 360582858726438577, 360582858560088858, 360582858258775224, 360582857925098903, 360582857586758398]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 67730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 67700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360554415345325820, 360554444851971702⟩, ⟨1923347032516357235, 1924697377153995135⟩, true⟩

def words04 : List Nat := [360582857248110379, 360582857127271292, 360582856788639575, 360582856310256781, 360582855831733389, 360582855223741254, 360582854782009015, 360582854466657132, 360582854151215995, 360582853669346669]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 67740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 67700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk677A
