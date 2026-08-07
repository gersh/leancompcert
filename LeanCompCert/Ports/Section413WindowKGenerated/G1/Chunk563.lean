import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk563

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362504277986855534, 362504324226577718⟩, ⟨(-1094502536616584070), (-1092743942493731558)⟩, true⟩

def state01 : KState := ⟨⟨362475000750807949, 362475047007668836⟩, ⟨553890537354609851, 555650096471797829⟩, true⟩

def words00 : List Nat := [371284915547455944, 371284915549352190, 371284915426001601, 371284915442985774, 371284915555053995, 371284915556950981, 371284915308491895, 371284915053949564, 371284914798636149, 371284914706061161]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 56300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 56300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362471218791483997, 362471265065431319⟩, ⟨766944291919959623, 768704813259647071⟩, true⟩

def words01 : List Nat := [371284914671980100, 371284914813917238, 371284914955174480, 371284914957072162, 371284914734800935, 371284914530384456, 371284914422677978, 371284914424576461, 371284914183684509, 371284913943507663]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 56310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 56300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362469365519663436, 362469411810601268⟩, ⟨871419907195071334, 873181385527638740⟩, true⟩

def words02 : List Nat := [371284913702457513, 371284913658834605, 371284913618494918, 371284913738971211, 371284913809577437, 371284913811474389, 371284913462029210, 371284913279067243, 371284913095141927, 371284912989112322]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 56320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 56300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362475444881399128, 362475491189612878⟩, ⟨528944907685487132, 530707359259229060⟩, true⟩

def words03 : List Nat := [371284912715373625, 371284912374136774, 371284912032158380, 371284912005845818, 371284911837944437, 371284911734958785, 371284911631276385, 371284911516472227, 371284911080396973, 371284910915549322]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 56330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 56300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362475887236248817, 362475933561383133⟩, ⟨504060618181428357, 505824023147727597⟩, true⟩

def words04 : List Nat := [371284910854888656, 371284910856808239, 371284910775894621, 371284910632991726, 371284910489351724, 371284910403674976, 371284910159881457, 371284910117442790, 371284910074397622, 371284910030294362]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 56340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 56300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362490572343484350, 362490618685787288⟩, ⟨(-323527207294862440), (-321762834790818682)⟩, true⟩

def words05 : List Nat := [371284909956644808, 371284910043297089, 371284910248670258, 371284910250572370, 371284910129847094, 371284909967401151, 371284909804229495, 371284909730577459, 371284909619855901, 371284909723299206]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 56350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 56300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362477671171794058, 362477717531220306⟩, ⟨403582367371397357, 405347705032394445⟩, true⟩

def words06 : List Nat := [371284909825925302, 371284909827823506, 371284909510946072, 371284909475000591, 371284909495709152, 371284909497607624, 371284909137367036, 371284908777719651, 371284908417278963, 371284908372182386]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 56360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 56300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362463690571930636, 362463736948454267⟩, ⟨1191751177128065921, 1193517478654508997⟩, true⟩

def words07 : List Nat := [371284908248319205, 371284908252756126, 371284908254181521, 371284908228152054, 371284907826571619, 371284907400077811, 371284906972573805, 371284906860090239, 371284906486038095, 371284906112673042]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 56370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 56300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362478141659517225, 362478188053025963⟩, ⟨376986538982161243, 378753798215790087⟩, true⟩

def words08 : List Nat := [371284905738501508, 371284905573536860, 371284905250610146, 371284905242793068, 371284905234398346, 371284905149329316, 371284904787587716, 371284904721139567, 371284904734837684, 371284904736803509]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 56380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 56300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362477256013975437, 362477302424837675⟩, ⟨427001480555202544, 428769718436653566⟩, true⟩

def words09 : List Nat := [371284904619114525, 371284904502095691, 371284904579318400, 371284904657373423, 371284904830444579, 371284905004222013, 371284905118923446, 371284905120823053, 371284904857223178, 371284904724809957]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 56390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 56300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 56300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk563
