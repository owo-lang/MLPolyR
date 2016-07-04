fun serv n =
    CM.Server.start { name = n, pref = 0, pathtrans = NONE,
		      cmd = ("/Users/blume/bin/sml", ["@CMslave"]) };

