import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk769A

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

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk769A
