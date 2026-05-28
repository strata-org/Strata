ps -o pid=,comm= | awk '$2 != "zsh" {print $1}'
ps -o pid=,comm= | awk '$2 != "zsh" {print $1}' | xargs -r kill