import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk283

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575095219557545, 360575100012429469⟩, ⟨204404955134159009, 204496694221785591⟩, true⟩

def state01 : KState := ⟨⟨360591801811472631, 360591806607873696⟩, ⟨(-268756937210422233), (-268665098231231679)⟩, true⟩

def words00 : List Nat := [360582325789008217, 360582324987288667, 360582324932739786, 360582324653728757, 360582324374712118, 360582322796833117, 360582319976999902, 360582318401571171, 360582316826137610, 360582316830111299]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 28300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 28300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577201500920832, 360577206300875982⟩, ⟨144641415387075571, 144733355000074429⟩, true⟩

def words01 : List Nat := [360582316830444004, 360582316542478265, 360582316534732647, 360582317845000845, 360582318285980057, 360582318726983682, 360582318727316481, 360582318545307653, 360582317121983590, 360582316941942369]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 28310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 28300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360580771061281596, 360580775864759681⟩, ⟨43676692724580883, 43768732124684999⟩, true⟩

def words02 : List Nat := [360582317464718916, 360582318677188240, 360582319263708485, 360582319850224782, 360582319850539908, 360582319849284450, 360582320521570442, 360582321193878976, 360582321194218353, 360582320825300616]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 28320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 28300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360621445008923207, 360621449815929574⟩, ⟨(-1108865985053106521), (-1108773845679061431)⟩, true⟩

def words03 : List Nat := [360582321439330398, 360582322107958378, 360582323429653754, 360582324042525244, 360582324042869816, 360582323596731666, 360582323484835033, 360582324445758242, 360582325826632040, 360582327207493773]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 28330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 28300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360576389811906048, 360576394622479996⟩, ⟨167855595674150037, 167947836170329733⟩, true⟩

def words04 : List Nat := [360582327783978979, 360582327784353037, 360582327696049255, 360582327576447300, 360582327456755049, 360582327020058073, 360582325345122070, 360582322719395987, 360582320093782960, 360582318708411931]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 28340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 28300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360509915334231026, 360509920148324982⟩, ⟨2052909397771337197, 2053001738077842765⟩, true⟩

def words05 : List Nat := [360582319530652973, 360582320561847820, 360582320799293741, 360582320799667769, 360582319799367171, 360582318271165530, 360582316742966517, 360582315183922528, 360582313452993739, 360582310900725471]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 28350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 28300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360573921767838393, 360573926585463628⟩, ⟨237505500365420162, 237597940836609304⟩, true⟩

def words06 : List Nat := [360582308348552863, 360582306680942091, 360582305932569081, 360582306031615697, 360582306031961028, 360582305061906498, 360582303740231425, 360582302952398927, 360582302164510848, 360582301556941831]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 28360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 28300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360541482463850075, 360541487285045003⟩, ⟨1157963569467033069, 1158056111227737923⟩, true⟩

def words07 : List Nat := [360582301262086417, 360582300009049765, 360582298756030618, 360582297924050231, 360582297716449496, 360582297106842236, 360582296497240539, 360582295267778265, 360582294082290812, 360582292644848659]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 28370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 28300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360570765566698838, 360570770391415786⟩, ⟨326649577817330372, 326742219550857696⟩, true⟩

def words08 : List Nat := [360582291207381269, 360582290661808856, 360582289570215643, 360582287859632824, 360582286149114948, 360582283574562766, 360582281771067219, 360582281204123607, 360582280637179042, 360582279451632442]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 28380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 28300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360573583576336861, 360573588404594035⟩, ⟨246529187234098461, 246621929492253989⟩, true⟩

def words09 : List Nat := [360582279046560706, 360582278308110930, 360582278066756707, 360582278067131342, 360582277330865014, 360582275542441967, 360582273754073114, 360582272856196232, 360582272580743529, 360582272275350805]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 28390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 28300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 28300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk283
