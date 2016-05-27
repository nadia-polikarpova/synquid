n_str = ARGV[0]
if n_str == nil
  puts "usage: ruby gen-array-search.rb <n>"
  exit
end


def gen(n, filename)
newline="\n"
range = 0.upto(n-1)

sig = range.map{|i| 
  type = i == 0 ? "a" : "{a | _v > x#{i-1}}"
  "x#{i}: #{type}"
}.join(" -> #{newline}#{' ' * (11 + n.to_s.length)}")

constants = 0.upto(n).map{|i|
  "n#{i} :: {Int | _v == #{i}}"
}.join(newline)

xs = range.map{|i| "x#{i}"}.join(" ")

measures = range.map{|i|
  "measure at#{i} :: Array a -> a where Array#{n} #{xs} -> x#{i}"
}.join(newline)

constraint = ([
  "(k < at0 arr ==> _v == 0)", 
  "(k > at#{n-1} arr ==> _v == #{n})", 
] + 1.upto(n-1).map{|i|
  "((k > at#{i-1} arr && k < at#{i} arr) ==> _v == #{i})"
}).join(" && #{newline}                                          ")

out = <<-EOC
data Array a where
  Array#{n} :: #{sig} -> Array a

qualifier {x < y, x > y}

#{constants}

#{measures}

findIdx :: arr: Array a -> k: a -> {Int | #{constraint}}
findIdx = ??
EOC

if filename
  File.open(filename, "w") {|file| file.puts out}
else
  puts out
end

end

if n_str == "all"
  2.upto(6).each{|n| gen(n, "Array-Search-#{n}.sq")}
else
  n = n_str.to_i
  gen(n, nil)
end
