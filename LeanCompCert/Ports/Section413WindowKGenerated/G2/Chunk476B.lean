import LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk476A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk476B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk476A

def state06 : KState := ⟨⟨360604040376027076, 360604054570131484⟩, ⟨(-1017430660298593644), (-1016973528293877478)⟩, true⟩

def words05 : List Nat := [360582718675113594, 360582718334345383, 360582718090951112, 360582718091606644, 360582717750187199, 360582717026828438, 360582716303361992, 360582716027864674, 360582716476119091, 360582716924503112]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 47650 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 47600 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561172671517583, 360561186871870117⟩, ⟨1025607927007661555, 1026065356829233659⟩, true⟩

def words06 : List Nat := [360582717153622001, 360582717154277588, 360582716943872478, 360582716502041120, 360582716060048180, 360582715508282630, 360582714517032188, 360582713306855830, 360582712096603127, 360582711213318182]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 47660 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 47600 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360512219962384678, 360512234168909262⟩, ⟨3359485897819995702, 3359943621894079312⟩, true⟩

def words07 : List Nat := [360582710762333521, 360582710243715365, 360582709725052635, 360582708983707540, 360582708199579812, 360582707301061073, 360582706402396626, 360582705460712585, 360582704262441611, 360582702785140262]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 47670 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 47600 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360557407326918443, 360557421539634337⟩, ⟨1204739035290761764, 1205197054596609462⟩, true⟩

def words08 : List Nat := [360582701307752420, 360582700269174975, 360582699453177586, 360582698895332669, 360582698337451176, 360582697304530692, 360582695938800636, 360582694855454772, 360582693771962259, 360582693023270249]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 47680 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 47600 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360566770792444929, 360566785011420509⟩, ⟨758059153261170412, 758517471122372690⟩, true⟩

def words09 : List Nat := [360582692493969717, 360582691625950410, 360582690757842253, 360582690141570567, 360582689745698451, 360582689240256748, 360582688734763009, 360582687948861895, 360582687177819514, 360582686845196660]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 47690 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 47600 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 47600 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk476B
