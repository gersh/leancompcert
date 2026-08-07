import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk396

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478502256843324, 362478524491163516⟩, ⟨264316546371886142, 264911529388622034⟩, true⟩

def state01 : KState := ⟨⟨362479379669551904, 362479401915410649⟩, ⟨229584977720484737, 230180417724227157⟩, true⟩

def words00 : List Nat := [371285214468179934, 371285214469477220, 371285214081143903, 371285213667289694, 371285213252971907, 371285212991398188, 371285212731325012, 371285212920899090, 371285213083408056, 371285213084754861]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 39600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 39600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362504228872940738, 362504251130533586⟩, ⟨(-754907206532228274), (-754311301681243124)⟩, true⟩

def words01 : List Nat := [371285212976343585, 371285213015283524, 371285213315501777, 371285213316800881, 371285212933227273, 371285212489349231, 371285212152802393, 371285212154246768, 371285212479348755, 371285212961338431]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 39610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 39600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362482687990469058, 362482710259763126⟩, ⟨98639232941736391, 99235601455549385⟩, true⟩

def words02 : List Nat := [371285213418293744, 371285213419600756, 371285213831210110, 371285214356524559, 371285215067272665, 371285215068571008, 371285214931079188, 371285214572888953, 371285214310805058, 371285214312285346]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 39620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 39600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362478390456482419, 362478412737477646⟩, ⟨269112130072140244, 269708962363521584⟩, true⟩

def words03 : List Nat := [371285214823315422, 371285215398045397, 371285215850963563, 371285215901201277, 371285216144189031, 371285216387807117, 371285217050781532, 371285217052080327, 371285216867351758, 371285216697174002]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 39630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 39600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362490490593054645, 362490512885701947⟩, ⟨(-210598654895084843), (-210001360658024131)⟩, true⟩

def words04 : List Nat := [371285216610152199, 371285216611582920, 371285216609767477, 371285216842692831, 371285216972773954, 371285216974073526, 371285216370178900, 371285216241044947, 371285216507031139, 371285216641958838]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 39640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 39600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362487318619803041, 362487340924251856⟩, ⟨(-84800893098604680), (-84203130869801968)⟩, true⟩

def words05 : List Nat := [371285216776365845, 371285216911194770, 371285217509400873, 371285217791706425, 371285217968977542, 371285218146726237, 371285218324066894, 371285218325366436, 371285217797825219, 371285217852950835]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 39650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 39600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362485855671747909, 362485877987786072⟩, ⟨(-26714063704532228), (-26115841781921732)⟩, true⟩

def words06 : List Nat := [371285218305200310, 371285218306522344, 371285218231970919, 371285218169991029, 371285218237276875, 371285218238718101, 371285218691743500, 371285219236781868, 371285219659196320, 371285219677136431]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 39660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 39600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362523317628781136, 362523339956594363⟩, ⟨(-1513001253680227708), (-1512402564584673268)⟩, true⟩

def words07 : List Nat := [371285220329740592, 371285220983015158, 371285222155482380, 371285222569961591, 371285222832644409, 371285223095735271, 371285223682475277, 371285224009661846, 371285224971127412, 371285225933142720]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 39670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 39600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362481088933109308, 362481111272672377⟩, ⟨162775613311474312, 163374768699737608⟩, true⟩

def words08 : List Nat := [371285226894732128, 371285227010808135, 371285227387587523, 371285227764991446, 371285228334788131, 371285228336088586, 371285228060338004, 371285227785178054, 371285227541460705, 371285227542984792]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 39680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 39600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362445559524620352, 362445581875868496⟩, ⟨1573241356871171532, 1573840976100906020⟩, true⟩

def words09 : List Nat := [371285227800133688, 371285228161487372, 371285228480325511, 371285228481626303, 371285228038672949, 371285227658230005, 371285227277131470, 371285227091648638, 371285226222540364, 371285225225392449]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 39690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 39600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 39600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk396
