import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk828

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362492592953051464, 362492696029686876⟩, ⟨(-619013674806390369), (-613250727849636709)⟩, true⟩

def state01 : KState := ⟨⟨362489761551275484, 362489864653510165⟩, ⟨(-384554815767435012), (-378789749058997524)⟩, true⟩

def words00 : List Nat := [371285289921778496, 371285289983947283, 371285290017863632, 371285290052685045, 371285290131038910, 371285290142227971, 371285290243512204, 371285290346003796, 371285290447487771, 371285290505763381]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 82800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 82800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362503936458159271, 362504039586279467⟩, ⟨(-1558412130726802371), (-1552644920307563693)⟩, true⟩

def words01 : List Nat := [371285290708833938, 371285290913357668, 371285291262303249, 371285291444094429, 371285291601775781, 371285291760388477, 371285291977704482, 371285292132824617, 371285292361148793, 371285292590706997]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 82810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 82800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489468681970067, 362489571835997438⟩, ⟨(-360181081958145460), (-354411725778239470)⟩, true⟩

def words02 : List Nat := [371285292813972720, 371285292843609197, 371285292933385287, 371285293024734500, 371285293157325992, 371285293160197072, 371285293098606214, 371285293037877581, 371285293048131401, 371285293103086110]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 82820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 82800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486613206940919, 362486716386876359⟩, ⟨(-123641476295880619), (-117869974022052095)⟩, true⟩

def words03 : List Nat := [371285293216614241, 371285293331314633, 371285293444719774, 371285293447591575, 371285293385448825, 371285293369311876, 371285293477865801, 371285293501255286, 371285293520578910, 371285293541014744]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 82830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 82800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489535383462787, 362489638589089692⟩, ⟨(-365723468784185151), (-359949838097050965)⟩, true⟩

def words04 : List Nat := [371285293598123483, 371285293601288366, 371285293680589722, 371285293778546005, 371285293839265364, 371285293842141515, 371285293792633510, 371285293843268474, 371285293989394784, 371285294044810238]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 82840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 82800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362485126329722499, 362485229561508498⟩, ⟨(-374022234587240), 5401775869545472⟩, true⟩

def words05 : List Nat := [371285294099097383, 371285294154402303, 371285294318557780, 371285294411280557, 371285294534781816, 371285294659405825, 371285294777833410, 371285294780713590, 371285294750367623, 371285294753107214]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 82850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 82800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362479826257871704, 362479929515238677⟩, ⟨438824730076526068, 444602647955284142⟩, true⟩

def words06 : List Nat := [371285294827381409, 371285294830267700, 371285294765953028, 371285294681849047, 371285294596608903, 371285294557105270, 371285294501677871, 371285294543473121, 371285294573782085, 371285294576756178]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 82860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 82800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362500114128409641, 362500217411831630⟩, ⟨(-1242541838405504843), (-1236761761220642073)⟩, true⟩

def words07 : List Nat := [371285294580303196, 371285294650136315, 371285294778349996, 371285294781242474, 371285294779420252, 371285294758893360, 371285294848643655, 371285294907956387, 371285295089954811, 371285295273329192]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 82870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 82800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362489788356947825, 362489891666280019⟩, ⟨(-386720332783676462), (-380938108025370640)⟩, true⟩

def words08 : List Nat := [371285295455515960, 371285295479994954, 371285295649179796, 371285295819819415, 371285295989343296, 371285295992216628, 371285295967855961, 371285295916991639, 371285295956513462, 371285296015268144]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 82880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 82800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362488728977087353, 362488832312270150⟩, ⟨(-298833974448595414), (-293049606803759892)⟩, true⟩

def words09 : List Nat := [371285296218270710, 371285296422425724, 371285296625310455, 371285296728806857, 371285296859173314, 371285296991020419, 371285297228643221, 371285297287090893, 371285297331901865, 371285297377748206]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 82890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 82800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 82800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk828
