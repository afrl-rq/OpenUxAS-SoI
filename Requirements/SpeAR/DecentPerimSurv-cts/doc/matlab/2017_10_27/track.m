function forplotting = track(N, velocity, T)

% initial conditions
t = 0;
P = 1;

%___________________________________________
% Position 1 is closest to base station
% Position N is farthest from base station
% Base station at 0
% Perimeter length of 1
%___________________________________________

pos = sort(rand(N,1));      % positions
vel = sign(rand(N,1)-0.5);  % 1 increasing, -1 decreasing
% vel = velocity*ones(N,1);
pos = sort([1e-2, 2e-2, 3e-2, 4e-2, 5e-2, 6e-2, 7e-2, 8e-2]);
vel = velocity*ones(N,1);

for n=1:N,
   uav(n).x   = pos(n);
   uav(n).v   = vel(n);
   uav(n).nl  = 0;        % # UAVs to left
   uav(n).nr  = 0;        % # UAVs to right
   uav(n).pl  = 0;        % estimate of perimeter to left
   uav(n).pr  = 0;        % estimate of perimeter to right
   uav(n).tr  = -1;       % ID of UAV to left
   uav(n).tl  = -1;       % ID of UAV to right
   uav(n).cr  = false;    % right neighbor has a right neighbor
   uav(n).cl  = false;    % left neighbor has a left neighbor
   uav(n).p   = -1;       % intermediate goal
end;

forplotting = t;
for n=1:N,
    forplotting = [forplotting, uav(n).x];
end;
forplotting = [forplotting, P];
for n=1:N,
    forplotting = [forplotting, uav(n).v];
end;
forplotting = [forplotting, zeros(1,2*N+1)];

% [0,v,ignore,ignore,ignore]  P = v for all time
% [1,A,w,offset,phase]        P = A*cos(w*t+phase)+offset
% [2,v_0,v_f,t_s,ignore]      P = v_0 for t < t_s, P = v_f for t >= t_s
% [3,v_0,v_g,ignore,ignore]   P = v_0 + v_g*t
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Ptype = [0,1,0,0,0];              % constant
% Ptype = [1, .3, 1, 1, pi/2];      % cos wave (note: A*w needs to be < 1)
Ptype = [2,1,1.3,4];                % step at t=4
% Ptype = [3, 1, .1*velocity, 0, 0];% ramp with slope .1

while t < T,
   % switch from initial perimeter type to cos wave
   % note: must ensure perimeter does not immediately shrink
   % otherwise perimeter end; detection could miss vehicles
   if t >= 8,
      Ptype = [1, .3, 1, 1.0, -2]; 
   end;
   
   % calculate next rend;ezvous time
   r = [];
   
   % calculate rend;ezvous time for each uav to goal
   for n=1:N,
      if uav(n).p >= 0,
         r = [r, abs(uav(n).x - uav(n).p)/velocity];
      else
         r = [r, inf];
      end;
   end;

   % calculate rendezvous time for UAV 1 reaching end of perimeter
   if uav(1).v > 0, % increasing
      r = [r, inf];
   else % decreasing
      r = [r, uav(1).x/velocity];
   end;

   % calculate rendezvous time for initial meeting of middle UAVs
   for n=2:N,
      a = n-1; % left neighbor
      if uav(n).v < uav(a).v,
         r = [r, abs(uav(n).x - uav(a).x)/2/velocity];
      else
         r = [r, inf];
      end;
   end;
   
   % calculate rendezvous time for UAV N reaching end of perimeter
   if uav(N).v > 0, % increasing
      switch Ptype(1),
         case 1,    % cos wave
            A = Ptype(2)/velocity;
            w = Ptype(3);
            c = (uav(N).x - Ptype(4))/velocity - t;
            [y, v] = fminbnd(@(x) (x-A*cos(w*x+Ptype(5))+c)^2,t,t+2/velocity);
            yb = y;
            it = 0;
            while v < 1e-4 && it < 10,
               yb = y;
               [y, v] = fminbnd(@(x) (x-A*cos(w*x+Ptype(5))+c)^2,t,t+0.9*(y-t));
               it = it + 1;
            end;
            r = [r, yb-t];
         case 2,    % step
            if t + (Ptype(2) - uav(N).x)/velocity >= Ptype(4),
               r = [r, (Ptype(3) - uav(N).x)/velocity];
            else
               r = [r, (Ptype(2) - uav(N).x)/velocity];
            end;
         case 3,    %ramp
            r = [r, (Ptype(2)+velocity*t - uav(N).x)/(velocity - Ptype(3)) - t];
         otherwise, % constant
            r = [r, (Ptype(2) - uav(N).x)/velocity];
      end;
   else % decreasing
      r = [r, inf];
   end;

   % find time of first event
   rmin = min(r);
   
   % update perimeter for time = t+rmin
   switch Ptype(1),
      case 1,
         P = Ptype(2)*cos(Ptype(3)*(t+rmin)+Ptype(5)) + Ptype(4);
      case 2,
         if rmin + t >= Ptype(4),
            P = Ptype(3);
         else
            P = Ptype(2);
         end;
      case 3,
         P = Ptype(2) + Ptype(3)*(t+rmin);
      otherwise,
         P = Ptype(2);
   end;
   
   % update all UAVs for time = t+rmin
   for n=1:N,
      uav(n).x = uav(n).x + rmin*uav(n).v;
      uav(n).pl = uav(n).pl + rmin*uav(n).v;
      uav(n).pr = uav(n).pr - rmin*uav(n).v;
   end;
   
   % update simulated time
   t = t + rmin;

   % find indices of all events happening at rmin
   ind = sort(find( abs(r - rmin) < 1e-12));
   
   % process events
   for i=1:length(ind),
      if ind(i) <= N, % UAV with ID ind(i) reached goal
         uav = UpdateUav(uav, ind(i), 'goal');
      end;
      if ind(i) >= N+2 && ind(i) <= 2*N, % two UAV rend;ezvous
         right = ind(i) - N; % right UAV in rend;ezvous
         left  = right - 1;  % left UAV in rend;ezvous
         uav = UpdateUav(uav, right, 'as_right');
         uav = UpdateUav(uav, left, 'as_left');
      end;
      if ind(i) == N+1,
         uav = UpdateUav(uav,1,'left_perimeter');
      end;
      if ind(i) == 2*N+1,
         uav = UpdateUav(uav,N,'right_perimeter');
      end;
   end;

   % save information for plotting
   v = t;
   for n=1:N,
      v = [v, uav(n).x];
   end;
   v = [v, P];
   for n=1:N,
      v = [v, uav(n).v];
   end;
   z = zeros(1,2*N+1);
   z(ind) = 1;
   v = [v, z];
   forplotting = [forplotting; v];
end;
end

function updated = UpdateUav(uav, i, eventtype)

if strcmp(eventtype,'update_from_left'),
    disp(['Update from left for ', num2str(i)]);
    j = i-1;
    uav(i).pl = uav(j).pl;
    uav(i).nl = uav(j).nl + 1;
    if uav(j).tl >= 0,
        uav(i).cl = true;
    end;
    if uav(i).tr >= 0,
        uav = UpdateUav(uav, uav(i).tr, 'update_from_left');
    end;
    uav = GoalUpdate(uav, i);
end;

if strcmp(eventtype,'update_from_right'),
    disp(['Update from right for ', num2str(i)]);
    j = i+1;
    uav(i).pr = uav(j).pr;
    uav(i).nr = uav(j).nr + 1;
    if uav(j).tr >= 0,
        uav(i).cr = true;
    end;
    if uav(i).tl >= 0,
        uav = UpdateUav(uav, uav(i).tl, 'update_from_right');
    end;
    uav = GoalUpdate(uav, i);
end;

if strcmp(eventtype,'as_right'),
    disp(['-As Right- update for ', num2str(i)]);
    if uav(i).tl < 0,
        j = i-1;
        uav(i).tl = j;
        uav(i).pl = uav(j).pl;
        uav(i).nl = uav(j).nl + 1;
        if uav(j).tl >= 0,
            uav(i).cl = true;
        end;
        if uav(i).tr >= 0,
            uav = UpdateUav(uav, uav(i).tr, 'update_from_left');
        end;
        uav = GoalUpdate(uav, i);
    end;
end;

if strcmp(eventtype,'as_left'),
    disp(['-As Left- update for ', num2str(i)]);
    if uav(i).tr < 0,
        j = i+1;
        uav(i).tr = j;
        uav(i).pr = uav(j).pr;
        uav(i).nr = uav(j).nr + 1;
        if uav(j).tr >= 0,
            uav(i).cr = true;
        end;
        if uav(i).tl >= 0,
            uav = UpdateUav(uav, uav(i).tl, 'update_from_right');
        end;
        uav = GoalUpdate(uav, i);
    end;
end;

if strcmp(eventtype,'left_perimeter'),
    disp(['Left perimeter update for ', num2str(i)]);
    if uav(i).tl < 0,
        uav(i).pl = 0;
        uav(i).nl = 0;
        if uav(i).tr >= 0,
            uav = UpdateUav(uav, uav(i).tr, 'update_from_left');
        end;
        uav = GoalUpdate(uav, i);
    else
        disp(['Error when meeting left perimeter. Should not have left neighbors, but travling with', num2str(uav(i).tl)]);
    end;
    uav(i).v = abs(uav(i).v);
end;

if strcmp(eventtype,'right_perimeter'),
    disp(['Right perimeter update for ', num2str(i)]);
    if uav(i).tr < 0,
        uav(i).pr = 0;
        uav(i).nr = 0;
        if uav(i).tl >= 0,
            uav = UpdateUav(uav, uav(i).tl, 'update_from_right');
        end;
        uav = GoalUpdate(uav, i);
    else
        disp(['Error when meeting right perimeter. Should not have right neighbors, but travling with ', num2str(uav(i).tr)]);
    end;
    uav(i).v = -abs(uav(i).v);
end;

if strcmp(eventtype,'goal'),
    disp(['Reached goal for ', num2str(i)]);
    uav = GoalUpdate(uav, i);
end;

updated = uav;
end

function updated = GoalUpdate(uav, i)
disp(['  >> ', num2str(i), ':  TL ', num2str(uav(i).tl), ', TR ', num2str(uav(i).tr)]);

% reset goal to none
uav(i).p = -1;

% calculate estimated team size
N = uav(i).nr + uav(i).nl + 1;

% calculate estimated perimeter length
P = uav(i).pr + uav(i).pl;

% calculate relative index
n = uav(i).nl + 1;

% calculate preferred segment end;points
yl = (n-2)*P/N;
xl = (n-1)*P/N;
xr = (n+0)*P/N;
yr = (n+1)*P/N;

% Calculate goal locations, min tie breaks to left
% p = argmin_{x={xl,xr}} ||x_i - x||
p = xl;
if abs(uav(i).x - xl) > abs(uav(i).x - xr),
    p = xr;
end;

% pl = argmin_{x={yl,xl}} ||x_i - x||
pl  = yl;
if abs(uav(i).x - yl) > abs(uav(i).x - xl),
    pl = xl;
end;

% pr = argmin_{x={xr,yr}} ||x_i - x||
pr = xr;
if abs(uav(i).x - xr) > abs(uav(i).x - yr),
    pr = yr;
end;

% choose preferred escort location for i
if uav(i).tr >= 0 && uav(i).tl >= 0,
    uav(i).p = p;
elseif uav(i).tr >= 0,
    uav(i).p = xr;
elseif uav(i).tl >= 0,
    uav(i).p = xl;
end;

% left neighbor committed to travel with i if no other neighbors
if ~uav(i).cl,
    pl = xl;
end;

% right neighbor committed to travel with i if no other neighbors
if ~uav(i).cr,
    pr = xr;
end;

% if reached left goal location
if uav(i).p >= 0 && abs(uav(i).p - uav(i).x) < 1e-12 && abs(uav(i).p - xl) < 1e-12,
    %if there is a neighbor to the left
    if uav(i).tl >= 0,
        % successful escort with TL_i, so separate and monitor own segment
        disp(['  Left escort complete for agent ', num2str(i), ' now going right']);
        uav(i).p = xr;
        uav(i).tl = -1;
        uav(i).cl = false;
        % inform right neighbor that no longer in clique
        if uav(i).tr >= 0,
            disp(['  Sending update to ', num2str(uav(i).tr)]);
            uav = UpdateUav(uav, uav(i).tr, 'update_from_left');
        else
            disp('  No right neighbor to update');
        end;
    end;
end;

% if reached right goal location
if uav(i).p >= 0 && abs(uav(i).p - uav(i).x) < 1e-12 && abs(uav(i).p - xr) < 1e-12,
    %if there is a neighbor to the right
    if uav(i).tr >= 0,
        % successful escort with TR_i, so separate and monitor own segment
        disp(['  Right escort complete for agent ', num2str(i), ' now going left']);
        uav(i).p = xl;
        uav(i).tr = -1;
        uav(i).cr = false;
        % inform left neighbor that no longer in clique
        if uav(i).tl >= 0,
            disp(['  Sending update to ', num2str(uav(i).tl)]);
            uav = UpdateUav(uav, uav(i).tl, 'update_from_right');
        else
            disp('  No left neighbor to update');
        end;
    end;
end;

% if left neighbor reached a goal
if uav(i).tl >= 0 && uav(i).cl && abs(uav(i).x - pl) < 1e-12,
    % TL_i successfully escorted its left neighbor
    uav(i).cl = false;
end;

% if right neighbor reached a goal
if uav(i).tr >= 0 && uav(i).cr && abs(uav(i).x - pr) < 1e-12,
    % TR_i successfully escorted its right neighbor
    uav(i).cr = false;
end;

% set velocity appropriate to reach goal
if uav(i).p >= 0 && uav(i).p <= uav(i).x,
    uav(i).v = -abs(uav(i).v);
elseif uav(i).p >=0 && uav(i).p >= uav(i).x,
    uav(i).v = abs(uav(i).v);
end;

% predict velocity for left neighbor
vl = uav(i).v;
if pl < uav(i).x,
    vl = -abs(uav(i).v);
elseif pl > uav(i).x,
    vl = abs(uav(i).v);
end;

% predict velocity for right neighbor
vr = uav(i).v;
if pr < uav(i).x,
    vr = -abs(uav(i).v);
elseif pr > uav(i).x,
    vr = abs(uav(i).v);
end;

% if not yet reached goal location
if uav(i).p >= 0 && abs(uav(i).p - uav(i).x) >= 1e-12,
    % if not going the same direction as left neighbor
    if abs(vl - uav(i).v) >= 1e-12,
        % no longer traveling with left neighbor
        uav(i).tl = -1;
        uav(i).cl = false;
    end;
    % if not going the same direction as right neighbor
    if abs(vr - uav(i).v) >= 1e-12,
        % no longer traveling with right neighbor
        uav(i).tr = -1;
        uav(i).cr = false;
    end;
end;

% no intermediate goals without neighbors
if uav(i).tl < 0 && uav(i).tr < 0,
    uav(i).p = -1;
end;

disp(['  << ', num2str(i), ':  TL ', num2str(uav(i).tl), ', TR ', num2str(uav(i).tr)]);

updated = uav;
end
