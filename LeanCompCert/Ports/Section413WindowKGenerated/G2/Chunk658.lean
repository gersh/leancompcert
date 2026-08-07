import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk658

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360580547604411517, 360580575372410125⟩, ⟨153440058917683877, 154674296677949349⟩, true⟩

def state01 : KState := ⟨⟨360600849390944450, 360600877167696578⟩, ⟨(-1182497854541221862), (-1181263040755528788)⟩, true⟩

def words00 : List Nat := [360582926099446951, 360582926366610260, 360582926742937619, 360582927119430043, 360582927284906037, 360582927383627408, 360582927384392956, 360582927369452653, 360582927568791456, 360582927842496300]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 65800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 65800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360574265476849066, 360574293262431965⟩, ⟨567164145656000490, 568399540639689902⟩, true⟩

def words01 : List Nat := [360582928000551981, 360582928158704019, 360582928284356574, 360582928588607501, 360582928834765824, 360582929081069940, 360582929184507440, 360582929185435233, 360582929058645762, 360582928928500633]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 65810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 65800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570106680502716, 360570134474835345⟩, ⟨840800670642004647, 842036641576105929⟩, true⟩

def words02 : List Nat := [360582928798064714, 360582928662309069, 360582928296327482, 360582927776679157, 360582927256887484, 360582926676479091, 360582926251394807, 360582926056929677, 360582925862353208, 360582925552483471]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 65820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 65800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360603083400604357, 360603111203691897⟩, ⟨(-1330271250160887680), (-1329034702848237312)⟩, true⟩

def words03 : List Nat := [360582925395022472, 360582925432139077, 360582925615595533, 360582925616523525, 360582925570039598, 360582925301384042, 360582925032558975, 360582925070617337, 360582925377961463, 360582925685506447]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 65830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 65800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602751809352852, 360602779621292949⟩, ⟨(-1308480026044802956), (-1307242895836770448)⟩, true⟩

def words04 : List Nat := [360582925831725012, 360582925984192557, 360582926366783114, 360582926749644783, 360582927004341358, 360582927317223208, 360582927501717385, 360582927686306869, 360582927791898451, 360582928094424158]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 65840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 65800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360596230424181122, 360596258244864460⟩, ⟨(-878954909644547128), (-877717203650452866)⟩, true⟩

def words05 : List Nat := [360582928626920300, 360582929159578041, 360582929571802231, 360582929883320129, 360582930136856261, 360582930390648681, 360582930679862621, 360582931025782753, 360582931228967469, 360582931432279616]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360621965304092271, 360621993133545183⟩, ⟨(-2574040929740809269), (-2572802646138215429)⟩, true⟩

def words06 : List Nat := [360582931798118671, 360582932279994088, 360582932720047190, 360582933160251512, 360582933404044282, 360582933418052060, 360582933662056025, 360582933906331761, 360582934340307865, 360582934934244456]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360587409299036098, 360587437137339828⟩, ⟨(-297607946054983538), (-296369079405938172)⟩, true⟩

def words07 : List Nat := [360582935378524094, 360582935822881093, 360582936367134440, 360582937027003038, 360582937528567204, 360582938030264277, 360582938353644263, 360582938447321495, 360582938516363767, 360582938585717875]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360596233045904213, 360596260892949083⟩, ⟨(-879008248300427380), (-877768805740738392)⟩, true⟩

def words08 : List Nat := [360582938884831439, 360582938954347843, 360582938955175334, 360582938909394675, 360582938863443393, 360582938785850399, 360582938949696814, 360582939113716671, 360582939161737877, 360582939364883934]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360608946257194079, 360608974113018297⟩, ⟨(-1716826011338123937), (-1715585990264906661)⟩, true⟩

def words09 : List Nat := [360582939562283171, 360582939759940727, 360582940139948359, 360582940366979403, 360582940379370172, 360582940391831611, 360582940392586735, 360582940544933764, 360582940940731456, 360582941336728637]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk658
