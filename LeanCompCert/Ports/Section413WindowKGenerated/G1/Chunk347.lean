import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk347

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362525611917004581, 362525628804976283⟩, ⟨(-1415080759611583321), (-1414684703832888311)⟩, true⟩

def state01 : KState := ⟨⟨362513065253868713, 362513082151994918⟩, ⟨(-979755484833008875), (-979359076641524265)⟩, true⟩

def words00 : List Nat := [371284862112512633, 371284862150385722, 371284863018660862, 371284863887494985, 371284864791287958, 371284865137181708, 371284865424098703, 371284865711367244, 371284866677451725, 371284867491609406]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 34700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 34700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362491715106663381, 362491732014953895⟩, ⟨(-238456548698641630), (-238059787653304762)⟩, true⟩

def words01 : List Nat := [371284869011710081, 371284870532190117, 371284871852363582, 371284872329909934, 371284872985082906, 371284873640769781, 371284875000373273, 371284875254616164, 371284875452945889, 371284875651725495]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 34710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 34700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362499834591379665, 362499851509740154⟩, ⟨(-520302384808996608), (-519905274081387242)⟩, true⟩

def words02 : List Nat := [371284876679900004, 371284877300344604, 371284878460738988, 371284879621510048, 371284880662239094, 371284880710884520, 371284880727186881, 371284880744061280, 371284881589940723, 371284882022133078]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 34720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 34700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362520031173211051, 362520048101837595⟩, ⟨(-1221852286693969704), (-1221454819373828770)⟩, true⟩

def words03 : List Nat := [371284882307400249, 371284882593013041, 371284883568187885, 371284884239081188, 371284885162396014, 371284886086108848, 371284887006399168, 371284887190631487, 371284888203512550, 371284889216964569]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 34730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 34700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362499072012144918, 362499088950819707⟩, ⟨(-493611691030699234), (-493213874582768336)⟩, true⟩

def words04 : List Nat := [371284890569513184, 371284891033037407, 371284891425648780, 371284891818627426, 371284892464077182, 371284892698311409, 371284893760800359, 371284894823700025, 371284895744627614, 371284896154221544]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 34740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 34700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362531170945358584, 362531187894228547⟩, ⟨(-1609280181978456321), (-1608882011196990689)⟩, true⟩

def words05 : List Nat := [371284896976166969, 371284897798661727, 371284899207823333, 371284899513875549, 371284899603943718, 371284899694332054, 371284900612522610, 371284901117207967, 371284902449583755, 371284903782402162]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 34750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 34700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362514023677425752, 362514040636473181⟩, ⟨(-1013131619732350248), (-1012733095129793130)⟩, true⟩

def words06 : List Nat := [371284905111689268, 371284905967186182, 371284907650249754, 371284909333786966, 371284911079781729, 371284911723302641, 371284912369128244, 371284913015304444, 371284914000294493, 371284914839253378]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 34760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 34700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362474158880393742, 362474175849590118⟩, ⟨373223234200978545, 373622111731926755⟩, true⟩

def words07 : List Nat := [371284915928726883, 371284917018579710, 371284918043245234, 371284918044373563, 371284918035368445, 371284918105420177, 371284918902401720, 371284918903530107, 371284918598605419, 371284918290985516]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 34770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 34700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362497578622218592, 362497595601534126⟩, ⟨(-441350552591767932), (-440951323065471194)⟩, true⟩

def words08 : List Nat := [371284918501157336, 371284918818312393, 371284919474329045, 371284920130768644, 371284920651637036, 371284920652765880, 371284920160249610, 371284920249760103, 371284920943171567, 371284921308669148]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 34780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 34700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362476804867927858, 362476821857529660⟩, ⟨281559346778899713, 281958934215810271⟩, true⟩

def words09 : List Nat := [371284921670916332, 371284922033533181, 371284922812071610, 371284923178060393, 371284923796182101, 371284924414689742, 371284924877726796, 371284924878856041, 371284924357169391, 371284924125754253]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 34790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 34700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 34700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk347
