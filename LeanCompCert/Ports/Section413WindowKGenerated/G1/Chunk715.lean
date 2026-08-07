import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk715

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362477349104156191, 362477425099236969⟩, ⟨555390062103800167, 559059658329574019⟩, true⟩

def state01 : KState := ⟨⟨362487849325779217, 362487925342762357⟩, ⟨(-195373081836239883), (-191701919479530349)⟩, true⟩

def words00 : List Nat := [371285244069776292, 371285244072484805, 371285244237302211, 371285244419277708, 371285244541482598, 371285244543934038, 371285244405294938, 371285244407020727, 371285244569430595, 371285244609455880]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 71500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 71500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362477253390193031, 362477329429573911⟩, ⟨562444684940458490, 566117449070795346⟩, true⟩

def words01 : List Nat := [371285244617758709, 371285244626945258, 371285244763985973, 371285244825064802, 371285244944318953, 371285245064492423, 371285245186124311, 371285245188576120, 371285245049607878, 371285244942004991]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 71510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 71500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362483168895043540, 362483244956256234⟩, ⟨139353810885567709, 143028136541238199⟩, true⟩

def words02 : List Nat := [371285244874467412, 371285244876935947, 371285244744860017, 371285244613300821, 371285244480830380, 371285244410663215, 371285244359915665, 371285244434031530, 371285244508258114, 371285244510800359]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 71520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 71500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362495787836327083, 362495863919719113⟩, ⟨(-763350430338887202), (-759674518083679584)⟩, true⟩

def words03 : List Nat := [371285244632600057, 371285244783620988, 371285244952892613, 371285244955345978, 371285244900748615, 371285244825579507, 371285244866737148, 371285244889027699, 371285245039134323, 371285245190345975]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 71530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 71500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362480438069833039, 362480514175350428⟩, ⟨334795243576645104, 338472738792307300⟩, true⟩

def words04 : List Nat := [371285245340302739, 371285245342755554, 371285245266707109, 371285245304155530, 371285245365924535, 371285245368377713, 371285245195135013, 371285244982528746, 371285244768950560, 371285244751713703]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 71540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 71500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362479640312696224, 362479716440326424⟩, ⟨391941864322863195, 395620941820133107⟩, true⟩

def words05 : List Nat := [371285244816313176, 371285244948071183, 371285245037623596, 371285245040125003, 371285245007509642, 371285244984153804, 371285245108195683, 371285245110650504, 371285245035513234, 371285244961033805]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 71550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 71500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362497092976417467, 362497169126054830⟩, ⟨(-857062001365400847), (-853381348925376029)⟩, true⟩

def words06 : List Nat := [371285244889816316, 371285244892520008, 371285244902594079, 371285245006986285, 371285245089737169, 371285245092207603, 371285245064344813, 371285245132137854, 371285245393608014, 371285245562755095]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 71560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 71500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362497149291198201, 362497225463142356⟩, ⟨(-861081129952592212), (-857398880899810450)⟩, true⟩

def words07 : List Nat := [371285245731514336, 371285245901077628, 371285246213576409, 371285246439004847, 371285246669463650, 371285246900849645, 371285247093691735, 371285247100552928, 371285247269561372, 371285247439911334]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 71570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 71500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490622667727559, 362490698861561047⟩, ⟨(-393821391298803648), (-390137575293587646)⟩, true⟩

def words08 : List Nat := [371285247772975975, 371285247944344393, 371285248100112161, 371285248256739013, 371285248456467163, 371285248571010353, 371285248808480878, 371285249046934698, 371285249249084453, 371285249327746831]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 71580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 71500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362503340312663005, 362503416528706445⟩, ⟨(-1304321162828554308), (-1300635756701020546)⟩, true⟩

def words09 : List Nat := [371285249534267345, 371285249742074823, 371285250143497318, 371285250285794924, 371285250382639688, 371285250480250353, 371285250771737089, 371285250966659489, 371285251222047431, 371285251478543724]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 71590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 71500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 71500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk715
