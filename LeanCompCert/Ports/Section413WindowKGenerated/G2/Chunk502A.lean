import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk502A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360563051703019539, 360563067517334995⟩, ⟨946591074439621307, 947127502364976605⟩, true⟩

def state01 : KState := ⟨⟨360594403830611964, 360594419651468942⟩, ⟨(-627412693095551556), (-626875936752793016)⟩, true⟩

def words00 : List Nat := [360581934223786489, 360581933983496586, 360581934171434366, 360581934402764381, 360581934403403393, 360581934294842410, 360581934246764321, 360581934421168631, 360581934569358216, 360581934818728053]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 50200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 50200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360592958720740846, 360592974548215241⟩, ⟨(-554895296250135179), (-554358207614871373)⟩, true⟩

def words01 : List Nat := [360581934819362020, 360581934759361092, 360581934936372337, 360581935374072906, 360581935539824280, 360581935705678203, 360581935706297038, 360581935732706474, 360581935953078840, 360581936173678397]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 50210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 50200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360596401231163101, 360596417065159036⟩, ⟨(-727835843026703708), (-727298426846535450)⟩, true⟩

def words02 : List Nat := [360581936789746082, 360581937010586263, 360581937032964377, 360581937055417779, 360581937056009182, 360581936747749900, 360581937125728196, 360581937512928309, 360581937700976317, 360581937989949574]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 50220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 50200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360605853813794392, 360605869654347166⟩, ⟨(-1202629645809951583), (-1202091900247646191)⟩, true⟩

def words03 : List Nat := [360581938674331919, 360581939358908198, 360581940354105955, 360581940954223068, 360581941183099028, 360581941412019891, 360581941701461168, 360581942188335174, 360581942665168895, 360581943142131095]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 50230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 50200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360610188413699237, 360610204260853807⟩, ⟨(-1420634816650662977), (-1420096739381745659)⟩, true⟩

def words04 : List Nat := [360581943420796969, 360581943421490622, 360581943457080568, 360581943609910442, 360581943610493720, 360581943635595640, 360581943636219842, 360581943527862236, 360581943628432344, 360581944191613758]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 50240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 50200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk502A
