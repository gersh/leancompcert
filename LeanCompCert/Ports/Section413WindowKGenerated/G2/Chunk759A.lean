import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk759A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360588631347605238, 360588668715609613⟩, ⟨(-492692995770305736), (-490777357411274292)⟩, true⟩

def state01 : KState := ⟨⟨360565300263145476, 360565337641341396⟩, ⟨1278193038874239262, 1280109450824105594⟩, true⟩

def words00 : List Nat := [360582202775922201, 360582202777003595, 360582202683798320, 360582202503805143, 360582202323645265, 360582202007283710, 360582201777439525, 360582201599518919, 360582201421466395, 360582201156699374]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 75900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 75900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360572742313589725, 360572779701987716⟩, ⟨713171633850843090, 715088820290803500⟩, true⟩

def words01 : List Nat := [360582200935431549, 360582200686549557, 360582200437356949, 360582200361719650, 360582200112841651, 360582199698519951, 360582199284002267, 360582199000238688, 360582198803067438, 360582198680126426]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 75910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 75900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360572453012131330, 360572490410846406⟩, ⟨735130322307246509, 737048292070058705⟩, true⟩

def words02 : List Nat := [360582198557027413, 360582198347235276, 360582198332469788, 360582198365905843, 360582198366812369, 360582198355951939, 360582198171847489, 360582197901052028, 360582197630071926, 360582197355296164]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 75920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 75900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360553073811200562, 360553111220101131⟩, ⟨2206740337813558065, 2208659081012526937⟩, true⟩

def words03 : List Nat := [360582197273740606, 360582197320230414, 360582197321214831, 360582197212664563, 360582196930836023, 360582196605500553, 360582196279835526, 360582196127604378, 360582195866935609, 360582195485060475]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 75930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 75900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360588768477429634, 360588805896561812⟩, ⟨(-504137325064037254), (-502217804828220018)⟩, true⟩

def words04 : List Nat := [360582195102950289, 360582194894386034, 360582194772188066, 360582194589871968, 360582194407469774, 360582194073107171, 360582193772810019, 360582193615026023, 360582193456929003, 360582193504298008]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 75940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 75900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk759A
