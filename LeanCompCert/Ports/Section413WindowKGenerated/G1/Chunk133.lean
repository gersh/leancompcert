import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk133

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479662620995916, 362479664905303129⟩, ⟨64361079292518493, 64381635314238399⟩, true⟩

def state01 : KState := ⟨⟨362531811081704029, 362531813369570118⟩, ⟨(-629326377285070903), (-629305773911590929)⟩, true⟩

def words00 : List Nat := [371284509608710133, 371284511180261614, 371284517378980337, 371284523576931815, 371284528892380024, 371284528892778350, 371284526811528351, 371284526932465450, 371284532694931956, 371284536247347025]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 13300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 13300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362538075855105331, 362538078146609476⟩, ⟨(-712585043760442489), (-712564391946552333)⟩, true⟩

def words01 : List Nat := [371284538733232337, 371284541218881587, 371284549343194999, 371284555442203530, 371284563199565993, 371284570955911780, 371284578382209682, 371284578382608364, 371284582320887385, 371284586337289864]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 13310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 13300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362450537600491237, 362450539895552764⟩, ⟨453666315533137169, 453687014749657025⟩, true⟩

def words02 : List Nat := [371284590908862241, 371284590909261024, 371284587981376934, 371284585048449919, 371284582115816541, 371284579552742663, 371284574452647354, 371284574716411240, 371284574930004481, 371284574930417705]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 13320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 13300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362614002632647662, 362614004931313009⟩, ⟨(-1726182993437989678), (-1726162246164437238)⟩, true⟩

def words03 : List Nat := [371284575448223590, 371284578518847384, 371284586374505267, 371284587866500101, 371284587930180719, 371284587993973888, 371284593675941714, 371284597760181220, 371284607461140197, 371284617160818711]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 13330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 13300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362507313312619192, 362507315614891343⟩, ⟨(-302455951214301564), (-302435155807322192)⟩, true⟩

def words04 : List Nat := [371284626852088648, 371284631914209755, 371284639799479923, 371284647683777800, 371284655952400978, 371284656747581329, 371284657493658183, 371284658239751411, 371284661295648623, 371284662992929893]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 13340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 13300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362447916917496585, 362447919223372808⟩, ⟨491123138695261049, 491143982234905631⟩, true⟩

def words05 : List Nat := [371284668064586090, 371284673135646592, 371284678200332863, 371284678322362018, 371284680100940209, 371284681879456613, 371284686793102966, 371284686793502812, 371284684248911463, 371284681497492188]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 13350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 13300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362490876895775590, 362490879205237087⟩, ⟨(-82975616210088763), (-82954724752819531)⟩, true⟩

def words06 : List Nat := [371284680553687087, 371284680554128516, 371284681162086359, 371284682170368112, 371284682170683148, 371284681489481881, 371284674558404697, 371284673221136181, 371284674662949585, 371284675127400514]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 13360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 13300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362469523706585189, 362469526019689912⟩, ⟨202842189617156379, 202863129802940519⟩, true⟩

def words07 : List Nat := [371284675588360295, 371284676049382123, 371284680984623941, 371284683167159914, 371284686870208672, 371284690572865407, 371284693414449507, 371284693414849978, 371284688821337372, 371284687688584004]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 13370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 13300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362440956523912988, 362440958840584131⟩, ⟨585328925296999666, 585349913220342084⟩, true⟩

def words08 : List Nat := [371284691000585099, 371284691000985734, 371284688015200570, 371284684980783037, 371284681946655348, 371284680570996810, 371284676889900210, 371284676023431134, 371284675156960412, 371284674293401185]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 13380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 13300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362569468116315059, 362569470436623784⟩, ⟨(-1136332346604405925), (-1136311309956361535)⟩, true⟩

def words09 : List Nat := [371284671029138566, 371284670070652101, 371284672328538119, 371284672328939429, 371284669298557139, 371284665673950875, 371284663986052464, 371284664755624803, 371284671084679885, 371284677412972090]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 13390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 13300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 13300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk133
