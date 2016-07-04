#!/bin/sh

for i in `ls *.mlpr`
do
	echo "testing $i"
	NAME=`echo "$i" | sed 's/.mlpr//g'`
	cd ..
	echo "***	compile $i"
	sml @SMLload=mlpolyr Tests2/$i
	echo "***	run $NAME"
	Tests2/$NAME
	echo "***	end of $NAME"
	echo ""
	cd Tests2
done
