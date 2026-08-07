import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk246

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362494406384042030, 362494414630915482⟩, ⟨(-215044358213541612), (-214907191201663612)⟩, true⟩

def state01 : KState := ⟨⟨362450625795932326, 362450634049712177⟩, ⟨862229901610265718, 862367238555851278⟩, true⟩

def words00 : List Nat := [371285680698300125, 371285680699075798, 371285680274460938, 371285679750442934, 371285679226189647, 371285678626500867, 371285677199712410, 371285676599791642, 371285675999650923, 371285675384070400]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 24600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 24600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362509079728692374, 362509087989484665⟩, ⟨(-576520076994844637), (-576382567437016693)⟩, true⟩

def words01 : List Nat := [371285674190202118, 371285674420530621, 371285676024327869, 371285676025104684, 371285675802242959, 371285675271258195, 371285675603273616, 371285675884934559, 371285676836409520, 371285677788134720]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 24610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 24600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362497719879048566, 362497728146850052⟩, ⟨(-296821680470885333), (-296683998311515565)⟩, true⟩

def words02 : List Nat := [371285678649521965, 371285678650302168, 371285678890811039, 371285679837428826, 371285681301019956, 371285681404671462, 371285681497589667, 371285681590754772, 371285682510629324, 371285683000558326]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 24620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 24600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362472370026506439, 362472378301321819⟩, ⟨327842183649109927, 327980038595527481⟩, true⟩

def words03 : List Nat := [371285685140401329, 371285687280392139, 371285688930988631, 371285688931765681, 371285688746322898, 371285688806103548, 371285690231326950, 371285690232104192, 371285689718843238, 371285689179511573]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 24630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 24600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362493037243385254, 362493045525152584⟩, ⟨(-181435776846864764), (-181297750569341940)⟩, true⟩

def words04 : List Nat := [371285689307162064, 371285689308026447, 371285690281556957, 371285691365867873, 371285692262852006, 371285692263629443, 371285690967110504, 371285690350971524, 371285690646025047, 371285690945193583]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 24640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 24600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362504272037729170, 362504280326574643⟩, ⟨(-458403646525764658), (-458265445735643938)⟩, true⟩

def words05 : List Nat := [371285690949499657, 371285690954049890, 371285692373599586, 371285693194364903, 371285694503366359, 371285695812569593, 371285697111772100, 371285697112549799, 371285696974204168, 371285697728718286]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 24650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 24600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479339182583434, 362479347478363908⟩, ⟨156622517067031428, 156760888911046192⟩, true⟩

def words06 : List Nat := [371285698874002733, 371285698966593527, 371285699049699671, 371285699133067373, 371285699705125162, 371285699705981998, 371285700234059837, 371285701006947753, 371285701790039880, 371285701790845102]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 24660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 24600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362530236011980658, 362530244314801487⟩, ⟨(-1099165109653563043), (-1099026564088670509)⟩, true⟩

def words07 : List Nat := [371285702920666986, 371285704308350944, 371285706522344825, 371285707316993010, 371285707728686384, 371285708140570035, 371285710195719546, 371285711448846637, 371285713253787857, 371285715058933060]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 24670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 24600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362505512285907221, 362505520595759868⟩, ⟨(-488821613443514023), (-488682894297547039)⟩, true⟩

def words08 : List Nat := [371285716819857822, 371285717482428926, 371285719787765463, 371285722093316935, 371285724886073576, 371285725492609530, 371285726055961817, 371285726619532046, 371285727849052424, 371285728651557627]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 24680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 24600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362487100820682206, 362487109137541484⟩, ⟨(-33981109849090250), (-33842217674834038)⟩, true⟩

def words09 : List Nat := [371285731095419690, 371285733539392240, 371285735973630238, 371285736223113042, 371285736563307281, 371285736903885359, 371285738885030889, 371285738950341566, 371285739006397576, 371285739062739864]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 24690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 24600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 24600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk246
