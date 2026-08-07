import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk759

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

def state06 : KState := ⟨⟨360571983349995927, 360572020779439272⟩, ⟨770801166531386442, 772721469950961926⟩, true⟩

def words05 : List Nat := [360582193505273145, 360582193471611481, 360582193542310784, 360582193734911022, 360582193813562682, 360582193892385468, 360582193893366635, 360582193838695519, 360582193653954534, 360582193521276436]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 75950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 75900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360584173116289311, 360584210555918547⟩, ⟨(-155224894258446887), (-153303817066579119)⟩, true⟩

def words06 : List Nat := [360582193388231466, 360582193355026775, 360582193247866398, 360582193054112183, 360582192860167904, 360582192622760282, 360582192581876848, 360582192648615297, 360582192649590242, 360582192630432947]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 75960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 75900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360585102888604122, 360585140338469463⟩, ⟨(-225971153154917432), (-224049298276717842)⟩, true⟩

def words07 : List Nat := [360582192653730073, 360582192677334536, 360582192691264882, 360582192692347369, 360582192533478888, 360582192226299426, 360582191918926792, 360582191638791325, 360582191544267096, 360582191584198307]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 75970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 75900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360571483410280966, 360571520870452293⟩, ⟨808764051428543406, 810686689405693038⟩, true⟩

def words08 : List Nat := [360582191585166168, 360582191508055554, 360582191257847013, 360582191180963200, 360582191103814944, 360582190880018313, 360582190483235045, 360582189999275864, 360582189515114852, 360582189204304191]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 75980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 75900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360563502388970111, 360563539859357069⟩, ⟨1415322361272858651, 1417245775585106177⟩, true⟩

def words09 : List Nat := [360582189097374714, 360582189131061729, 360582189132026733, 360582189066934066, 360582188828815645, 360582188547312358, 360582188265487724, 360582188156830639, 360582188074334997, 360582187830088452]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 75990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 75900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 75900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk759
