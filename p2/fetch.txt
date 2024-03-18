#!/bin/bash

[ $# -eq 1 ] || {
	echo "usage: $0 PUZZLE_ID" >&2
	exit 1
}

if [ ! -e "auth.txt" ]; then
	curl -s -L -b cookies.txt -c cookies.txt "https://www.kenkenpuzzle.com/play_now" \
	| sed -nE '/input.*authenticity_token/{s:.*auth.*value="([0-9a-zA-Z+/=]*)".*:\1:;p;q}' \
	> auth.txt
fi

curl -s -L -b cookies.txt -c cookies.txt \
	--data-urlencode "utf8=✓" \
	--data-urlencode "authenticity_token=$(cat auth.txt)" \
	--data-urlencode "puzzle_id=$1" \
	--data-urlencode "x=0" \
	--data-urlencode "y=0" \
	"https://www.kenkenpuzzle.com/find_puzzle" \
| sed -nE '/base64/{s:.*'"'"'([0-9a-zA-Z+/=]*)'"'"'.*:\1:;p;q}' \
| base64 -d