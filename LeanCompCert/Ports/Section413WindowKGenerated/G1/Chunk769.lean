import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk769

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362474848975246037, 362474937381279694⟩, ⟨784690806791691285, 789281731923880839⟩, true⟩

def state01 : KState := ⟨⟨362478775888983148, 362478864318762647⟩, ⟨482735797530643249, 487328548839435833⟩, true⟩

def words00 : List Nat := [371285200991260302, 371285200948543652, 371285200879871949, 371285200919360101, 371285200932866879, 371285200935518099, 371285200723530513, 371285200681817646, 371285200664331916, 371285200667076774]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 76900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 76900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362485052681790789, 362485141135751150⟩, ⟨(-25704442882117), 4568906736686957⟩, true⟩

def words01 : List Nat := [371285200586674460, 371285200508427964, 371285200516730359, 371285200523418544, 371285200580705862, 371285200639035255, 371285200696549004, 371285200699200753, 371285200531377547, 371285200533914654]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 76910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 76900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362468643781266830, 362468732258875022⟩, ⟨1262200435699240038, 1266796865991086676⟩, true⟩

def words02 : List Nat := [371285200609944902, 371285200612596734, 371285200464508027, 371285200252708957, 371285200039930511, 371285199842681071, 371285199559798507, 371285199418880547, 371285199277031862, 371285199136113955]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 76920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 76900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362486102760741606, 362486191262274046⟩, ⟨(-80984781086122100), (-76386510178247300)⟩, true⟩

def words03 : List Nat := [371285198923868849, 371285198837878919, 371285198813705716, 371285198816388621, 371285198781766533, 371285198698661325, 371285198614487282, 371285198570159432, 371285198453104132, 371285198468962571]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 76930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 76900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362483790843976906, 362483879369479268⟩, ⟨96874771203432979, 101474886473444887⟩, true⟩

def words04 : List Nat := [371285198480806435, 371285198483468611, 371285198411101774, 371285198461647906, 371285198515296128, 371285198517949109, 371285198368416370, 371285198216802022, 371285198078386637, 371285198081454232]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 76940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 76900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362476733703930203, 362476822253377613⟩, ⟨639972238323214026, 644574196283279386⟩, true⟩

def words05 : List Nat := [371285198119368318, 371285198175490322, 371285198224821112, 371285198227474166, 371285198071870124, 371285197969244675, 371285197888204943, 371285197890908180, 371285197803510602, 371285197697716014]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 76950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 76900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362488888227062739, 362488976800225182⟩, ⟨(-295445713072433121), (-290841929880512123)⟩, true⟩

def words06 : List Nat := [371285197650519690, 371285197653443559, 371285197786962891, 371285197939999780, 371285198051513495, 371285198054169313, 371285197997901691, 371285198015925723, 371285198157359080, 371285198209198945]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 76960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 76900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362487036628998736, 362487125226337559⟩, ⟨(-152900023158002566), (-148294378983976136)⟩, true⟩

def words07 : List Nat := [371285198260421365, 371285198312564831, 371285198453402873, 371285198510911036, 371285198618345969, 371285198726835704, 371285198836397335, 371285198839069253, 371285198821690238, 371285198849972171]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 76970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 76900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362480496284415130, 362480584905388801⟩, ⟨350625884157498669, 355233347863929329⟩, true⟩

def words08 : List Nat := [371285198996414985, 371285198999069560, 371285198944489720, 371285198876580586, 371285198807632727, 371285198775725262, 371285198787678247, 371285198872150071, 371285198921966446, 371285198924714219]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 76980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 76900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362489438713012532, 362489527358045540⟩, ⟨(-337894924849878241), (-333285608699077179)⟩, true⟩

def words09 : List Nat := [371285198975190218, 371285199087008723, 371285199226873663, 371285199229528237, 371285199163285122, 371285199055125405, 371285198965200530, 371285198968126991, 371285198970433475, 371285199029729037]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 76990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 76900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 76900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk769
