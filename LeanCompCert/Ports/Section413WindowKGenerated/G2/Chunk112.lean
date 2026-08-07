import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk112

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360549328776400506, 360549329466463182⟩, ⟨397384838172686510, 397390075699691402⟩, true⟩

def state01 : KState := ⟨⟨360628054564065828, 360628055255416606⟩, ⟨(-484677175680290512), (-484671923720030854)⟩, true⟩

def words00 : List Nat := [360584807893886352, 360584812277481065, 360584819209294417, 360584826139896153, 360584826366269001, 360584826366406148, 360584824584749967, 360584822553928051, 360584820523429681, 360584823436335344]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 11200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 11200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360632802011698172, 360632802704350218⟩, ⟨(-537784940483545874), (-537779673929745718)⟩, true⟩

def words01 : List Nat := [360584823436457166, 360584821716740178, 360584826182207082, 360584838662973204, 360584849072051958, 360584859479296971, 360584865906428956, 360584867979603106, 360584872251971459, 360584876523623924]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 11210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 11200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360566129052853498, 360566129746793738⟩, ⟨210256966349598724, 210262247363518200⟩, true⟩

def words02 : List Nat := [360584880033572508, 360584880033709350, 360584879332636768, 360584873224644091, 360584867117717439, 360584858840001182, 360584855637392864, 360584856701433931, 360584856701556095, 360584853010138664]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 11220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 11200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360668823316099983, 360668824011332264⟩, ⟨(-943943620142304940), (-943938324612215224)⟩, true⟩

def words03 : List Nat := [360584851343144594, 360584850775593321, 360584854447903460, 360584854914674311, 360584854914802624, 360584847970122683, 360584841026653058, 360584836649063065, 360584843733200179, 360584851204232165]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 11230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 11200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360637547771132877, 360637548467673270⟩, ⟨(-592254139912404588), (-592248829672804832)⟩, true⟩

def words04 : List Nat := [360584854658273676, 360584862781818952, 360584878760050028, 360584894735479004, 360584906153663989, 360584909753482495, 360584909753604876, 360584907957396042, 360584906161482087, 360584908806338918]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 11240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 11200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360630339230335985, 360630339928168378⟩, ⟨(-510849647405425684), (-510844322624334394)⟩, true⟩

def words05 : List Nat := [360584921331952663, 360584933855366405, 360584940417753554, 360584944817838344, 360584947163920789, 360584949509624938, 360584959693995366, 360584967841338925, 360584971870955049, 360584975899873881]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 11250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 11200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360799870068739485, 360799870767869016⟩, ⟨(-2420735080059410348), (-2420729740666070888)⟩, true⟩

def words06 : List Nat := [360584987763004655, 360585003587301363, 360585019177807410, 360585034765570599, 360585043634466308, 360585048404009890, 360585056272710949, 360585064140056415, 360585076646990896, 360585095704372781]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 11260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 11200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360727742042669777, 360727742743106462⟩, ⟨(-1607487755634469470), (-1607482401502865332)⟩, true⟩

def words07 : List Nat := [360585108893112050, 360585122079525538, 360585143080217923, 360585168021628119, 360585186705455038, 360585205385989735, 360585217976979827, 360585222802994628, 360585235437852388, 360585248070515126]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 11270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 11200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360717884121499785, 360717884823231816⟩, ⟨(-1496550834713629969), (-1496545465964179829)⟩, true⟩

def words08 : List Nat := [360585264651132950, 360585273468801393, 360585278353954198, 360585283238259232, 360585283785827511, 360585290695543211, 360585305402767705, 360585320107413092, 360585329865962537, 360585341605982310]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 11280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 11200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360711388460277900, 360711389163310320⟩, ⟨(-1423689218012103895), (-1423683834574707873)⟩, true⟩

def words09 : List Nat := [360585353121988356, 360585364635992889, 360585379609029515, 360585386835418934, 360585387276129818, 360585387716772325, 360585387716885082, 360585388292662847, 360585399443293912, 360585410591982588]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 11290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 11200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 11200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk112
