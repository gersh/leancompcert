import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk140

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362506547849706792, 362506550392276523⟩, ⟨(-305766918357731804), (-305742836186320298)⟩, true⟩

def state01 : KState := ⟨⟨362404016040855509, 362404018587219748⟩, ⟨1129861727177220395, 1129885862491363303⟩, true⟩

def words00 : List Nat := [371284714605830491, 371284714606251398, 371284709248318316, 371284705256101319, 371284701264247694, 371284698864971657, 371284690777778428, 371284681195244136, 371284671613902705, 371284667114164171]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 14000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 14000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362450572048936112, 362450574599090236⟩, ⟨477753330114637698, 477777518544487866⟩, true⟩

def words01 : List Nat := [371284661358364119, 371284660682569072, 371284660006735557, 371284659275823180, 371284656612638759, 371284655543867548, 371284657747091973, 371284657747513577, 371284655311835068, 371284652881440057]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 14010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 14000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362465439094922442, 362465441648855503⟩, ⟨269284924773386483, 269309166202966167⟩, true⟩

def words02 : List Nat := [371284650451214194, 371284650095398792, 371284649685537699, 371284651407306217, 371284651407635999, 371284651052965823, 371284643937390942, 371284639898353555, 371284636884783547, 371284636885220647]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 14020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 14000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362466774078972817, 362466776636754884⟩, ⟨250704201217840564, 250728496667900522⟩, true⟩

def words03 : List Nat := [371284635517480129, 371284634136516009, 371284636435503884, 371284637588021064, 371284638893014851, 371284640197978210, 371284641505644065, 371284641506066111, 371284636063294265, 371284634791788211]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 14030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 14000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362431357065651567, 362431359627198505⟩, ⟨748459424085751237, 748483772414391131⟩, true⟩

def words04 : List Nat := [371284635920865448, 371284635921296008, 371284635226404239, 371284634440209462, 371284634157782102, 371284634158246981, 371284632669577536, 371284633200794217, 371284633201118601, 371284632493562519]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 14040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 14000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362511563545451592, 362511566110813140⟩, ⟨(-378851724815618030), (-378827322872135432)⟩, true⟩

def words05 : List Nat := [371284629958630736, 371284631215126318, 371284634244129574, 371284634244552108, 371284630538422477, 371284625943012851, 371284621797540791, 371284621798013384, 371284622488515763, 371284624405182521]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 14050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 14000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362406763320192488, 362406765889372721⟩, ⟨1094937735412022630, 1094962191065801286⟩, true⟩

def words06 : List Nat := [371284626185974526, 371284626186397405, 371284622190215320, 371284619396017566, 371284616602004261, 371284614279028789, 371284607192334860, 371284600065556854, 371284592939626486, 371284588362085287]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 14060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 14000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362351708413919611, 362351710986915424⟩, ⟨1870273183590132186, 1870297692948282364⟩, true⟩

def words07 : List Nat := [371284582831673413, 371284582337875141, 371284581844001221, 371284581347834722, 371284575315540062, 371284570650906400, 371284565986720408, 371284563381423350, 371284554064273973, 371284544629880501]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 14070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 14000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362441001989465139, 362441004566244068⟩, ⟨612819863930656763, 612844426575171807⟩, true⟩

def words08 : List Nat := [371284535196630655, 371284530792938006, 371284523879983786, 371284521995871514, 371284520111894534, 371284517459439459, 371284508101774351, 371284503770728237, 371284499557045972, 371284499557484322]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 14080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 14000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362451262716873361, 362451265297516582⟩, ⟨468089685905569414, 468114303017251054⟩, true⟩

def words09 : List Nat := [371284496471087553, 371284491466262236, 371284486461978151, 371284484595832913, 371284480693769793, 371284478359555267, 371284476025524349, 371284473123157957, 371284467247703465, 371284464893475253]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 14090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 14000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 14000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk140
