import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk443A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360638045785982852, 360638057975636007⟩, ⟨(-2427345776929978912), (-2426980854029528896)⟩, true⟩

def state01 : KState := ⟨⟨360614946934975880, 360614959130403114⟩, ⟨(-1404140769742613851), (-1403775591022563443)⟩, true⟩

def words00 : List Nat := [360583275072657424, 360583275887265046, 360583276689276028, 360583277491422956, 360583278163610823, 360583278327418857, 360583278327963741, 360583278221490868, 360583278344527833, 360583279060194305]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 44300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 44300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360539047285390289, 360539059486515833⟩, ⟨1959541109374520468, 1959906540615976632⟩, true⟩

def words01 : List Nat := [360583280143126126, 360583281226125513, 360583282053363633, 360583282372344993, 360583282561679212, 360583282751171316, 360583282751671774, 360583282730819825, 360583282201668048, 360583281204490021]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 44310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 44300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582029218009045, 360582041424852252⟩, ⟨54265804340193754, 54631489015832940⟩, true⟩

def words02 : List Nat := [360583280207220915, 360583279184189822, 360583278449797152, 360583278099175214, 360583277748517250, 360583276975729030, 360583275928746528, 360583275100809365, 360583274272732138, 360583273806738466]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 44320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 44300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590763211452399, 360590775424066872⟩, ⟨(-333031033086811602), (-332665092541871544)⟩, true⟩

def words03 : List Nat := [360583273779487928, 360583273359312434, 360583272939040081, 360583273005339482, 360583273041625533, 360583273078010430, 360583273078550219, 360583272859706924, 360583272827693957, 360583272997587049]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 44330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 44300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360556742909335077, 360556755127653305⟩, ⟨1175451868924646584, 1175818062402767876⟩, true⟩

def words04 : List Nat := [360583273048475719, 360583273049081808, 360583272592368844, 360583271807652769, 360583271022881316, 360583269885827731, 360583269057673088, 360583268580955236, 360583268104192686, 360583267372577832]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 44340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 44300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk443A
