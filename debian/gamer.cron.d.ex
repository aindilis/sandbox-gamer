#
# Regular cron jobs for the gamer package
#
0 4	* * *	root	[ -x /usr/bin/gamer_maintenance ] && /usr/bin/gamer_maintenance
